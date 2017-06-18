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

    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Arc, Mutex};
    use std::fs::File;
    use std::cell::UnsafeCell;
    use std::io::{Write, BufWriter};

    pub fn get_ts() -> Ts {
        Ts { time: EVENT_COUNTER.fetch_add(1, Ordering::Relaxed) }
    }

    #[must_use]
    pub struct Ts {
        time: u64,
    }

    pub fn empty_event(ts: Ts, stack: *const Stack, was_empty: bool) {
        log(Event::Empty {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            was_empty: was_empty,
        })
    }
    pub fn push_event(ts: Ts, stack: *const Stack, node: *const Node) {
        log(Event::Push {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            node: node,
        })
    }
    pub fn pop_event(ts: Ts, stack: *const Stack, popped: *const Node) {
        log(Event::Pop {
            ts: ts.time,
            id: get_id(),
            stack: stack,
            popped: popped,
        })
    }
    pub fn wait_event(ts: Ts, node: *const Node) {
        log(Event::Wait {
            ts: ts.time,
            id: get_id(),
            node: node,
        })
    }
    pub fn signal_event(ts: Ts, node: *const Node) {
        log(Event::Signal {
            ts: ts.time,
            id: get_id(),
            node: node,
        })
    }
    pub fn try_acquire_event(ts: Ts, mutex: *const RawMutex, acquired: bool) {
        log(Event::TryAcquire {
            ts: ts.time,
            id: get_id(),
            mutex: mutex,
            acquired: acquired,
        })
    }
    pub fn release_event(ts: Ts, mutex: *const RawMutex) {
        log(Event::Release {
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
            for buf in list.iter() {
                for &event in (*buf.cell.get()).buf.iter() {
                    log_event(&mut log_file, event);
                }
            }
        }
    }

    struct Buf {
        buf: Vec<Event>,
    }
    struct BufCell {
        cell: UnsafeCell<Buf>,
    }
    unsafe impl Sync for BufCell {}
    unsafe impl Send for BufCell {}

    static EVENT_COUNTER: AtomicU64 = AtomicU64::new(0);

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
            let buf = Arc::new(BufCell { cell: UnsafeCell::new(Buf { buf: Vec::new() }) });
            BUF_LIST.lock().unwrap().push(buf.clone());
            buf
        };
    }

    #[cold]
    fn do_log(buf: &mut Vec<Event>) {
        if let Ok(mut log) = LOG_FILE.try_lock() {
            match *log {
                Some(ref mut x) => {
                    for &event in buf.iter() {
                        log_event(x, event);
                    }
                    buf.clear();
                }
                None => unreachable!(),
            }
        }
    }

    fn log(event: Event) {
        LOCAL_BUF.with(|x| unsafe {
            let buf = &mut *x.cell.get();
            buf.buf.push(event);
            if 0 == backoff::thread_num(0, 4000) {
                do_log(&mut buf.buf);
            }
        });
    }

    fn get_id() -> u64 {
        unsafe { syscall!(GETTID) as u64 }
    }

    #[derive(Clone, Copy)]
    enum Event {
        Push {
            ts: u64,
            id: u64,
            stack: *const Stack,
            node: *const Node,
        },
        Pop {
            ts: u64,
            id: u64,
            stack: *const Stack,
            popped: *const Node,
        },
        Wait { ts: u64, id: u64, node: *const Node },
        Empty {
            ts: u64,
            id: u64,
            stack: *const Stack,
            was_empty: bool,
        },
        Signal { ts: u64, id: u64, node: *const Node },
        TryAcquire {
            ts: u64,
            id: u64,
            mutex: *const RawMutex,
            acquired: bool,
        },
        Release {
            ts: u64,
            id: u64,
            mutex: *const RawMutex,
        },
    }

    fn log_event(log: &mut BufWriter<File>, event: Event) {
        match event {
                Event::Empty { ts, id, stack, was_empty } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :empty }}\n {{:ts \
                              {ts}, :process {id}, :type :ok, :f :empty, :value {{ :stack \
                              {stack:?}, :was_empty {was_empty} }} }}",
                             ts = ts,
                             id = id,
                             stack = stack,
                             was_empty = was_empty)
                }

                Event::Push { ts, id, stack, node } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :push }} \n{{:ts {ts}, \
                              :process {id}, :type :ok, :f :push, :value {{ :stack {stack:?}, \
                              :node {node:?} }} }}",
                             ts = ts,
                             id = id,
                             stack = stack,
                             node = node)
                }
                Event::Pop { ts, id, stack, popped } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :pop }} \n{{:ts {ts}, \
                              :process {id}, :type :ok, :f :pop, :value {{ :stack {stack:?}, \
                              :popped {popped:?} }} }}",
                             ts = ts,
                             id = id,
                             stack = stack,
                             popped = popped)
                }
                Event::Wait { ts, id, node } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :wait }}\n{{:ts {ts}, \
                              :process {id}, :type :ok, :f :wait, :value {{ :node {node:?} }} }}",
                             ts = ts,
                             id = id,
                             node = node)
                }
                Event::Signal { ts, id, node } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :signal }}\n{{:ts \
                              {ts}, :process {id}, :type :ok, :f :signal, :value {{ :node \
                              {node:?} }} }}",
                             ts = ts,
                             id = id,
                             node = node)
                }
                Event::TryAcquire { ts, id, mutex, acquired } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :try_acquire }}\n{{:ts \
                              {ts}, :process {id}, :type :ok, :f :try_acquire, :value {{ :mutex \
                              {mutex:?}, :acquired {acquired} }}}}",
                             ts = ts,
                             id = id,
                             mutex = mutex,
                             acquired = acquired)
                }
                Event::Release { ts, id, mutex } => {
                    writeln!(log,
                             "{{:ts {ts}, :process {id}, :type :invoke, :f :release }}\n{{:ts \
                              {ts}, :process {id}, :type :ok, :f :release, :value {{ :mutex \
                              {mutex:?} }} }}",
                             ts = ts,
                             id = id,
                             mutex = mutex)
                }
            }
            .unwrap()
    }
}
