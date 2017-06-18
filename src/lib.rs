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
                let id = log::get_ts();
                self.stack.push(&mut node);
                log::push_event(id, &self.stack, &node);
            }

            self.flush();

            let id = log::get_ts();
            node.wait();
            log::wait_event(id, &node);
        }

        return QLockGuard { lock: self };
    }

    fn attempt_acquire(&self) -> bool {
        let mut counter = 0usize;
        loop {
            let id = log::get_ts();
            let acq_results = self.lock.try_acquire();
            log::try_acquire_event(id, &self.lock, acq_results);

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
            let id = log::get_ts();
            empty = self.stack.empty();
            log::empty_event(id, &self.stack, empty);
        }
        if empty {
            return;
        }

        let mut counter = 0usize;
        let mut yield_counter = 0usize;
        loop {
            let acquired;
            {
                let id = log::get_ts();
                acquired = self.lock.try_acquire();
                log::try_acquire_event(id, &self.lock, acquired);
            }
            if !acquired {
                return;
            }
            let popped;
            {
                let id = log::get_ts();
                popped = self.stack.pop();
                log::pop_event(id, &self.stack, popped);
            }
            if popped != dummy_node() {
                unsafe {
                    let pop_ref = &mut *popped;
                    let id = log::get_ts();
                    pop_ref.signal();
                    log::signal_event(id, pop_ref);
                }
                return;
            }

            let id = log::get_ts();
            self.lock.release();
            log::release_event(id, &self.lock);

            {
                let id = log::get_ts();
                empty = self.stack.empty();
                log::empty_event(id, &self.stack, empty);
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
            let id = log::get_ts();
            popped = self.lock.stack.pop();
            log::pop_event(id, &self.lock.stack, popped);
        }
        if popped != dummy_node() {
            unsafe {
                let pop_ref = &mut *popped;
                let id = log::get_ts();
                pop_ref.signal();
                log::signal_event(id, pop_ref);
            }
            return;
        }

        {
            let id = log::get_ts();
            self.lock.lock.release();
            log::release_event(id, &self.lock.lock);
        }

        self.lock.flush();
    }
}

#[cfg(not(feature = "lin-log"))]
mod log {
    use stack::{Node, Stack};
    use mutex::RawMutex;

    pub fn get_ts() -> Ts {
        Ts
    }

    #[must_use]
    pub struct Ts;

    pub fn empty_event(_ts: Ts, _stack: *const Stack, _was_empty: bool) {}
    pub fn push_event(_ts: Ts, _stack: *const Stack, _node: *const Node) {}
    pub fn pop_event(_ts: Ts, _stack: *const Stack, _popped: *const Node) {}
    pub fn wait_event(_ts: Ts, _node: *const Node) {}
    pub fn signal_event(_ts: Ts, _node: *const Node) {}
    pub fn try_acquire_event(_ts: Ts, _mutex: *const RawMutex, _acquired: bool) {}
    pub fn release_event(_ts: Ts, _mutex: *const RawMutex) {}
}

#[cfg(feature = "lin-log")]
mod log {
    use libc;

    use stack::{Node, Stack};
    use mutex::RawMutex;

    use qlock_util::backoff;

    use std::sync::atomic::{AtomicU32, Ordering};
    use std::sync::{Arc, Mutex};
    use std::fs::File;
    use std::cell::UnsafeCell;
    use std::io::{Write, BufWriter};

    pub fn get_ts() -> Ts {
        Ts { time: EVENT_COUNTER.fetch_add(1, Ordering::Relaxed) }
    }

    #[must_use]
    pub struct Ts {
        time: u32,
    }

    pub fn empty_event(ts: Ts, stack: *const Stack, was_empty: bool) {
        log(Empty {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            was_empty: was_empty,
        })
    }
    pub fn push_event(ts: Ts, stack: *const Stack, node: *const Node) {
        log(Push {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            node: node,
        })
    }
    pub fn pop_event(ts: Ts, stack: *const Stack, popped: *const Node) {
        log(Pop {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            popped: popped,
        })
    }
    pub fn wait_event(ts: Ts, node: *const Node) {
        log(Wait {
            ts: ts.time,
            id: get_id(),
            node: node,
        })
    }
    pub fn signal_event(ts: Ts, node: *const Node) {
        log(Signal {
            ts: ts.time,
            id: get_id(),
            node: node,
        })
    }
    pub fn try_acquire_event(ts: Ts, mutex: *const RawMutex, acquired: bool) {
        log(TryAcquire {
            ts: ts.time,
            id: get_id(),
            mutex: mutex,
            acquired: acquired,
        })
    }
    pub fn release_event(ts: Ts, mutex: *const RawMutex) {
        log(Release {
            ts: ts.time,
            id: get_id(),
            mutex: mutex,
        })
    }

    extern "C" fn on_exit() {
        unsafe {
            let mut list = Vec::new();
            list.append(&mut *BUF_LIST.lock().unwrap());

            let mut log_file = (*LOG_FILE.lock().unwrap()).take().unwrap();
            for buf_cell in list.iter() {
                let buf = &mut *buf_cell.cell.get();
                for event in buf.push_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.pop_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.wait_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.empty_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.signal_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.try_acquire_buf.iter() {
                    event.log(&mut log_file);
                }
                for event in buf.release_buf.iter() {
                    event.log(&mut log_file);
                }
            }
        }
    }

    struct Buf {
        push_buf: Vec<Push>,
        pop_buf: Vec<Pop>,
        wait_buf: Vec<Wait>,
        empty_buf: Vec<Empty>,
        signal_buf: Vec<Signal>,
        try_acquire_buf: Vec<TryAcquire>,
        release_buf: Vec<Release>,
    }

    struct BufCell {
        cell: UnsafeCell<Buf>,
    }
    unsafe impl Sync for BufCell {}
    unsafe impl Send for BufCell {}

    static EVENT_COUNTER: AtomicU32 = AtomicU32::new(0);

    lazy_static! {
        static ref BUF_LIST: Mutex<Vec<Arc<BufCell>>> = Mutex::new(Vec::new());

        static ref LOG_FILE: Mutex<Option<BufWriter<File>>> = {
            let file = File::create("linearizability.log").expect("cannot open file");
            let mutex = Mutex::new(Some(BufWriter::new(file)));
            unsafe {
                libc::atexit(on_exit);
            }
            mutex
        };
    }

    thread_local! {
        static LOCAL_BUF: Arc<BufCell> = {
            let buf = Arc::new(BufCell { cell: UnsafeCell::new(Buf {
                push_buf: Vec::new(),
                pop_buf: Vec::new(),
                wait_buf: Vec::new(),
                empty_buf: Vec::new(),
                signal_buf: Vec::new(),
                try_acquire_buf: Vec::new(),
                release_buf: Vec::new()
            }) });
            BUF_LIST.lock().unwrap().push(buf.clone());
            buf
        };
    }

    #[cold]
    fn do_log(buf: &mut Buf) {
        if let Ok(mut log) = LOG_FILE.try_lock() {
            match *log {
                Some(ref mut x) => {
                    for event in buf.push_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.pop_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.wait_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.empty_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.signal_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.try_acquire_buf.iter() {
                        event.log(x);
                    }
                    for event in buf.release_buf.iter() {
                        event.log(x);
                    }
                    buf.push_buf.clear();
                    buf.pop_buf.clear();
                    buf.wait_buf.clear();
                    buf.empty_buf.clear();
                    buf.signal_buf.clear();
                    buf.try_acquire_buf.clear();
                    buf.release_buf.clear();
                }
                None => unreachable!(),
            }
        }
    }

    fn log<T: Event>(event: T) {
        LOCAL_BUF.with(|x| unsafe {
            let buf = &mut *x.cell.get();
            event.push(buf);
            if 0 == backoff::thread_num(0, 4000) {
                do_log(buf);
            }
        });
    }

    fn get_id() -> u32 {
        unsafe { syscall!(GETTID) as u32 }
    }

    trait Event {
        fn log(&self, file: &mut BufWriter<File>);
        fn push(&self, buf: &mut Buf);
    }

    #[derive(Clone, Copy)]
    struct Push {
        ts: u32,
        id: u32,
        stack: *const Stack,
        node: *const Node,
    }
    impl Event for Push {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :push }} \n{{:ts {ts}, \
                      :process {id}, :type :ok, :f :push, :value {{ :stack {stack:?}, \
                      :node {node:?} }} }}",
                     ts = self.ts,
                     id = self.id,
                     stack = self.stack,
                     node = self.node)
                .unwrap()
        }

        fn push(&self, buf: &mut Buf) {
            buf.push_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct Pop {
        ts: u32,
        id: u32,
        stack: *const Stack,
        popped: *const Node,
    }
    impl Event for Pop {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :pop }} \n{{:ts {ts}, \
                      :process {id}, :type :ok, :f :pop, :value {{ :stack {stack:?}, \
                      :popped {popped:?} }} }}",
                     ts = self.ts,
                     id = self.id,
                     stack = self.stack,
                     popped = self.popped)
                .unwrap()
        }

        fn push(&self, buf: &mut Buf) {
            buf.pop_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct Wait {
        ts: u32,
        id: u32,
        node: *const Node,
    }
    impl Event for Wait {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :wait }}\n{{:ts {ts}, \
                      :process {id}, :type :ok, :f :wait, :value {{ :node {node:?} }} }}",
                     ts = self.ts,
                     id = self.id,
                     node = self.node)
                .unwrap()
        }
        fn push(&self, buf: &mut Buf) {
            buf.wait_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct Empty {
        ts: u32,
        id: u32,
        stack: *const Stack,
        was_empty: bool,
    }
    impl Event for Empty {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :empty }}\n {{:ts {ts}, \
                      :process {id}, :type :ok, :f :empty, :value {{ :stack {stack:?}, :was_empty \
                      {was_empty} }} }}",
                     ts = self.ts,
                     id = self.id,
                     stack = self.stack,
                     was_empty = self.was_empty)
                .unwrap()
        }

        fn push(&self, buf: &mut Buf) {
            buf.empty_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct Signal {
        ts: u32,
        id: u32,
        node: *const Node,
    }
    impl Event for Signal {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :signal }}\n{{:ts \
                      {ts}, :process {id}, :type :ok, :f :signal, :value {{ :node \
                      {node:?} }} }}",
                     ts = self.ts,
                     id = self.id,
                     node = self.node)
                .unwrap()
        }

        fn push(&self, buf: &mut Buf) {
            buf.signal_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct TryAcquire {
        ts: u32,
        id: u32,
        mutex: *const RawMutex,
        acquired: bool,
    }
    impl Event for TryAcquire {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :try_acquire }}\n{{:ts \
                      {ts}, :process {id}, :type :ok, :f :try_acquire, :value {{ :mutex \
                      {mutex:?}, :acquired {acquired} }}}}",
                     ts = self.ts,
                     id = self.id,
                     mutex = self.mutex,
                     acquired = self.acquired)
                .unwrap()
        }
        fn push(&self, buf: &mut Buf) {
            buf.try_acquire_buf.push(*self);
        }
    }

    #[derive(Clone, Copy)]
    struct Release {
        ts: u32,
        id: u32,
        mutex: *const RawMutex,
    }
    impl Event for Release {
        fn log(&self, log: &mut BufWriter<File>) {
            writeln!(log,
                     "{{:ts {ts}, :process {id}, :type :invoke, :f :release }}\n{{:ts \
                      {ts}, :process {id}, :type :ok, :f :release, :value {{ :mutex \
                      {mutex:?} }} }}",
                     ts = self.ts,
                     id = self.id,
                     mutex = self.mutex)
                .unwrap()
        }
        fn push(&self, buf: &mut Buf) {
            buf.release_buf.push(*self);
        }
    }
}
