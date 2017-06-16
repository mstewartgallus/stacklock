// Copyright 2017 Steven Stewart-Gallus
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied.  See the License for the specific language governing
// permissions and limitations under the License.
//
#![feature(asm)]
#![feature(integer_atomics)]
#![feature(const_fn)]

#[cfg(feature = "lin-log")]
#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate syscall;

extern crate libc;

extern crate qlock_util;

mod mutex;
mod stack;
mod notifier;

use qlock_util::backoff;

use stack::{Node, Stack, dummy_node};
use mutex::RawMutex;

const LOOPS: usize = 4;

pub struct QLock {
    stack: Stack,
    lock: RawMutex,
}
unsafe impl Send for QLock {}
unsafe impl Sync for QLock {}

pub struct QLockGuard<'r> {
    lock: &'r QLock,
}

impl QLock {
    pub fn new() -> Self {
        QLock {
            stack: Stack::new(),
            lock: RawMutex::new(),
        }
    }

    pub fn lock<'r>(&'r self) -> QLockGuard<'r> {
        // As an optimization spin a bit trying to get the lock before
        // falling back to a private node to spin on.
        if self.attempt_acquire() {
            return QLockGuard { lock: self };
        }

        {
            let mut node = Node::new();

            unsafe {
                let ev = log::push_event(&self.stack, &node);
                self.stack.push(&mut node);
                ev.complete();
            }

            self.flush();

            let ev = log::wait_event(&node);
            node.wait();
            ev.complete();
        }

        return QLockGuard { lock: self };
    }

    fn attempt_acquire(&self) -> bool {
        let mut counter = 0usize;
        loop {
            let ev = log::try_acquire_event(&self.lock);
            let acq_results = self.lock.try_acquire();
            ev.complete(acq_results);

            if acq_results {
                return true;
            }

            if counter > LOOPS {
                return false;
            }
            backoff::yield_now();

            let spins = backoff::thread_num(1, 1 << counter);

            backoff::pause_times(spins);

            counter = counter.wrapping_add(1);
        }
    }

    fn flush(&self) {
        let mut empty;
        {
            let ev = log::empty_event(&self.stack);
            empty = self.stack.empty();
            ev.complete(empty);
        }
        if empty {
            return;
        }

        let mut counter = 0usize;
        let mut yield_counter = 0usize;
        loop {
            let acquired;
            {
                let ev = log::try_acquire_event(&self.lock);
                acquired = self.lock.try_acquire();
                ev.complete(acquired);
            }
            if !acquired {
                return;
            }
            let popped;
            {
                let ev = log::pop_event(&self.stack);
                popped = self.stack.pop();
                ev.complete(popped);
            }
            if popped != dummy_node() {
                unsafe {
                    let pop_ref = &mut *popped;
                    let ev = log::signal_event(pop_ref);
                    pop_ref.signal();
                    ev.complete();
                }
                return;
            }

            let ev = log::release_event(&self.lock);
            self.lock.release();
            ev.complete();

            {
                let ev = log::empty_event(&self.stack);
                empty = self.stack.empty();
                ev.complete(empty);
            }
            if empty {
                return;
            }

            let interval = 8;
            if yield_counter % interval == interval - 1 {
                backoff::yield_now();
            }

            let spins = backoff::thread_num(1, 1 << counter);

            backoff::pause_times(spins);

            if counter < 4 {
                counter = counter.wrapping_add(1);
            }
            yield_counter = yield_counter.wrapping_add(1);
        }
    }
}

impl<'r> Drop for QLockGuard<'r> {
    fn drop(&mut self) {
        let popped;
        {
            let ev = log::pop_event(&self.lock.stack);
            popped = self.lock.stack.pop();
            ev.complete(popped);
        }
        if popped != dummy_node() {
            unsafe {
                let pop_ref = &mut *popped;
                let ev = log::signal_event(pop_ref);
                pop_ref.signal();
                ev.complete();
            }
            return;
        }

        {
            let ev = log::release_event(&self.lock.lock);
            self.lock.lock.release();
            ev.complete();
        }

        self.lock.flush();
    }
}

#[cfg(not(feature = "lin-log"))]
mod log {
    use stack::{Node, Stack};
    use mutex::RawMutex;

    pub struct EmptyEvent;
    pub fn empty_event(_stack_ptr: *const Stack) -> EmptyEvent {
        EmptyEvent
    }
    impl EmptyEvent {
        pub fn complete(self, _was_empty: bool) {}
    }

    pub struct PushEvent;
    pub fn push_event(_stack_ptr: *const Stack, _node: *const Node) -> PushEvent {
        PushEvent
    }
    impl PushEvent {
        pub fn complete(self) {}
    }

    pub struct PopEvent;
    pub fn pop_event(_stack_ptr: *const Stack) -> PopEvent {
        PopEvent
    }
    impl PopEvent {
        pub fn complete(self, _popped: *const Node) {}
    }

    pub struct WaitEvent;
    pub fn wait_event(_node_ptr: *const Node) -> WaitEvent {
        WaitEvent
    }
    impl WaitEvent {
        pub fn complete(self) {}
    }

    pub struct SignalEvent;
    pub fn signal_event(_node_ptr: *const Node) -> SignalEvent {
        SignalEvent
    }
    impl SignalEvent {
        pub fn complete(self) {}
    }

    pub struct TryAcquireEvent;
    pub fn try_acquire_event(_mutex_ptr: *const RawMutex) -> TryAcquireEvent {
        TryAcquireEvent
    }
    impl TryAcquireEvent {
        pub fn complete(self, _acquired: bool) {}
    }

    pub struct ReleaseEvent;
    pub fn release_event(_mutex_ptr: *const RawMutex) -> ReleaseEvent {
        ReleaseEvent
    }
    impl ReleaseEvent {
        pub fn complete(self) {}
    }
}

#[cfg(feature = "lin-log")]
mod log {
    use stack::{Node, Stack};
    use mutex::RawMutex;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Mutex;
    use std::fs::File;
    use std::io::{Write, BufWriter};

    lazy_static! {
        static ref LOG_FILE: Mutex<BufWriter<File>> = {
            let file = File::create("linearizability.log").expect("cannot open file");
            Mutex::new(BufWriter::new(file))
        };

        static ref EVENT_COUNTER: AtomicU64 = {
            AtomicU64::new(0)
        };
    }

    fn get_id() -> u64 {
        EVENT_COUNTER.fetch_add(1, Ordering::Relaxed)
    }

    pub struct EmptyEvent {
        id: u64,
    }
    pub fn empty_event(stack_ptr: *const Stack) -> EmptyEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :empty, :value {:?} }}",
                 id,
                 stack_ptr)
            .unwrap();
        EmptyEvent { id: id }
    }
    impl EmptyEvent {
        pub fn complete(self, was_empty: bool) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :empty, :value {} }}",
                     self.id,
                     was_empty)
                .unwrap();
        }
    }

    pub struct PushEvent {
        id: u64,
    }
    pub fn push_event(stack_ptr: *const Stack, node: *const Node) -> PushEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :push, :value (list {:?} {:?})}}",
                 id,
                 stack_ptr,
                 node)
            .unwrap();
        PushEvent { id: id }
    }
    impl PushEvent {
        pub fn complete(self) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :push, :value (list)}}",
                     self.id)
                .unwrap();
        }
    }

    pub struct PopEvent {
        id: u64,
    }
    pub fn pop_event(stack_ptr: *const Stack) -> PopEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :pop, :value {:?}}}",
                 id,
                 stack_ptr)
            .unwrap();
        PopEvent { id: id }
    }
    impl PopEvent {
        pub fn complete(self, popped: *const Node) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :pop, :value {:?}}}",
                     self.id,
                     popped)
                .unwrap();
        }
    }

    pub struct WaitEvent {
        id: u64,
    }
    pub fn wait_event(node_ptr: *const Node) -> WaitEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :wait, :value {:?}}}",
                 id,
                 node_ptr)
            .unwrap();
        WaitEvent { id: id }
    }
    impl WaitEvent {
        pub fn complete(self) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :wait, :value (list)}}",
                     self.id)
                .unwrap();
        }
    }

    pub struct SignalEvent {
        id: u64,
    }
    pub fn signal_event(node_ptr: *const Node) -> SignalEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :signal, :value {:?}}}",
                 id,
                 node_ptr)
            .unwrap();
        SignalEvent { id: id }
    }
    impl SignalEvent {
        pub fn complete(self) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :signal, :value (list)}}",
                     self.id)
                .unwrap();
        }
    }

    pub struct TryAcquireEvent {
        id: u64,
    }
    pub fn try_acquire_event(mutex_ptr: *const RawMutex) -> TryAcquireEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :try_acquire, :value {:?}}}",
                 id,
                 mutex_ptr)
            .unwrap();
        TryAcquireEvent { id: id }
    }
    impl TryAcquireEvent {
        pub fn complete(self, acquired: bool) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :try_acquire, :value {}}}",
                     self.id,
                     acquired)
                .unwrap();
        }
    }

    pub struct ReleaseEvent {
        id: u64,
    }
    pub fn release_event(mutex_ptr: *const RawMutex) -> ReleaseEvent {
        let id = get_id();
        writeln!(&mut *LOG_FILE.lock().unwrap(),
                 "{{:process {}, :type :invoke, :f :release, :value {:?}}}",
                 id,
                 mutex_ptr)
            .unwrap();
        ReleaseEvent { id: id }
    }
    impl ReleaseEvent {
        pub fn complete(self) {
            writeln!(&mut *LOG_FILE.lock().unwrap(),
                     "{{:process {}, :type :ok, :f :release, :value (list)}}",
                     self.id)
                .unwrap();
        }
    }
}
