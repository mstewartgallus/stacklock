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
#![feature(hint_core_should_pause)]

#[cfg(feature = "lin-log")]
#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate syscall;

extern crate libc;

extern crate sleepfast;

extern crate dontshare;
extern crate weakrand;

mod mutex;
mod stack;
mod notifier;

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::thread;

use stack::{Node, Stack};
use mutex::{RawMutex, SpinState};

const MAX_EXP: usize = 4;

pub struct Mutex<T: ?Sized> {
    stack: Stack,
    lock: RawMutex,
    data: UnsafeCell<T>,
}
unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}

pub struct MutexGuard<'r, T: ?Sized + 'r> {
    lock: &'r Mutex<T>,
    _phantom: PhantomData<&'r mut T>,
}

impl<T> Mutex<T> {
    pub fn new(val: T) -> Self {
        Mutex {
            stack: Stack::new(),
            lock: RawMutex::new(),
            data: UnsafeCell::new(val),
        }
    }

    pub fn into_inner(self) -> T {
        unsafe { self.data.into_inner() }
    }
}

impl<T: ?Sized> Mutex<T> {
    pub fn lock<'r>(&'r self) -> MutexGuard<'r, T> {
        // As an optimization spin a bit trying to get the lock before
        // falling back to a private node to spin on.
        let acquired;
        {
            let ts = log::get_ts();
            acquired = self.lock.spin_try_acquire();
            log::try_acquire_event(ts, &self.lock, acquired);
        }
        if acquired {
            return MutexGuard {
                lock: self,
                _phantom: PhantomData,
            };
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

        return MutexGuard {
            lock: self,
            _phantom: PhantomData,
        };
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
            if popped != ptr::null_mut() {
                unsafe {
                    let pop_ref = &mut *popped;
                    let id = log::get_ts();
                    pop_ref.signal();
                    log::signal_event(id, pop_ref);
                }
                return;
            }

            let id = log::get_ts();
            let spin_state = self.lock.release();
            log::release_event(id, &self.lock);

            if SpinState::Spinner == spin_state {
                return;
            }

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
                thread::yield_now();
            }

            let exp;
            if counter < MAX_EXP {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            } else {
                exp = 1 << MAX_EXP;
            }

            let spins = weakrand::rand(1, exp);

            sleepfast::pause_times(spins as usize);

            yield_counter = yield_counter.wrapping_add(1);
        }
    }
}

impl<'r, T: ?Sized> Drop for MutexGuard<'r, T> {
    fn drop(&mut self) {
        let spin_state;
        {
            let id = log::get_ts();
            spin_state = self.lock.lock.release();
            log::release_event(id, &self.lock.lock);
        }

        if spin_state != SpinState::Spinner {
            self.lock.flush();
        }
    }
}

impl<T: ?Sized + Default> Default for Mutex<T> {
    fn default() -> Mutex<T> {
        Mutex::new(Default::default())
    }
}

impl<'a, T: ?Sized + 'a> Deref for MutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
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

    use weakrand;

    use std::sync::atomic::{AtomicU32, ATOMIC_U32_INIT, Ordering};
    use std::sync::{Arc, Mutex};
    use std::fs::File;
    use std::cell::UnsafeCell;
    use std::io;
    use std::io::{Write, BufWriter};

    pub fn get_ts() -> Ts {
        Ts { time: EVENT_COUNTER.fetch_add(1, Ordering::Acquire) }
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

                let mut mem_buf = MemBuf { vec: Vec::new() };
                for event in buf.push_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.pop_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.wait_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.empty_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.signal_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.try_acquire_buf.iter() {
                    event.log(&mut mem_buf);
                }
                for event in buf.release_buf.iter() {
                    event.log(&mut mem_buf);
                }
                log_file.write(mem_buf.vec.as_ref()).unwrap();
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
        str_buf: MemBuf,
    }

    struct BufCell {
        cell: UnsafeCell<Buf>,
    }
    unsafe impl Sync for BufCell {}
    unsafe impl Send for BufCell {}

    static TID_COUNTER: AtomicU32 = ATOMIC_U32_INIT;
    static EVENT_COUNTER: AtomicU32 = ATOMIC_U32_INIT;

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
        static TID: u32 = {
            TID_COUNTER.fetch_add(1, Ordering::Relaxed)
        };

        static LOCAL_BUF: Arc<BufCell> = {
            let buf = Arc::new(BufCell { cell: UnsafeCell::new(Buf {
                push_buf: Vec::new(),
                pop_buf: Vec::new(),
                wait_buf: Vec::new(),
                empty_buf: Vec::new(),
                signal_buf: Vec::new(),
                try_acquire_buf: Vec::new(),
                release_buf: Vec::new(),
                str_buf: MemBuf { vec: Vec::new() }
            }) });
            BUF_LIST.lock().unwrap().push(buf.clone());
            buf
        };
    }
    struct MemBuf {
        vec: Vec<u8>,
    }
    impl Write for MemBuf {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.vec.extend_from_slice(buf);
            return Ok(buf.len());
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[cold]
    fn do_log(buf: &mut Buf) {
        for event in buf.push_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.pop_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.wait_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.empty_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.signal_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.try_acquire_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        for event in buf.release_buf.iter() {
            event.log(&mut buf.str_buf);
        }
        buf.push_buf.clear();
        buf.pop_buf.clear();
        buf.wait_buf.clear();
        buf.empty_buf.clear();
        buf.signal_buf.clear();
        buf.try_acquire_buf.clear();
        buf.release_buf.clear();

        if let Ok(mut log) = LOG_FILE.lock() {
            match *log {
                Some(ref mut x) => {
                    x.write(buf.str_buf.vec.as_ref()).unwrap();
                }
                None => unreachable!(),
            }
        }
        buf.str_buf.vec.clear();
    }

    fn log<T: Event>(event: T) {
        LOCAL_BUF.with(|x| unsafe {
            let buf = &mut *x.cell.get();
            event.push(buf);
            if 0 == weakrand::rand(0, 4000) {
                do_log(buf);
            }
        });
    }

    fn get_id() -> u32 {
        TID.with(|x| *x)
    }

    trait Event {
        fn log<B: Write>(&self, log: &mut B);
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :push }}\n{{:ts {ts},\
                      :process 0x{id:x},:type :ok,:f :push,:value{{:stack {stack:?},\
                      :node {node:?}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :pop}}\n{{:ts {ts},\
                      :process 0x{id:x},:type :ok,:f :pop,:value{{:stack {stack:?},\
                      :popped {popped:?}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :wait}}\n{{:ts {ts},\
                      :process 0x{id:x},:type :ok,:f :wait,:value{{:node {node:?}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :empty}}\n{{:ts {ts},\
                      :process 0x{id:x},:type :ok,:f :empty,:value{{:stack {stack:?},\
                      :was_empty {was_empty}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :signal}}\n{{:ts \
                      {ts},:process 0x{id:x},:type :ok,:f :signal,:value{{:node \
                      {node:?}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :try_acquire}}\n{{:ts \
                      {ts},:process 0x{id:x},:type :ok,:f :try_acquire,:value{{:mutex \
                      {mutex:?},:acquired {acquired}}}}}",
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
        fn log<B: Write>(&self, log: &mut B) {
            writeln!(log,
                     "{{:ts {ts},:process 0x{id:x},:type :invoke,:f :release}}\n{{:ts \
                      {ts},:process 0x{id:x},:type :ok,:f :release,:value{{:mutex \
                      {mutex:?}}}}}",
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
