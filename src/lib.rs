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

#[macro_use]
extern crate syscall;

extern crate libc;

extern crate qlock_util;

mod mutex;
mod stack;
mod notifier;


use stack::{Node, Stack, dummy_node};
use mutex::RawMutex;

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
        unsafe {
            {
                let mut node = Node::new();
                self.stack.push(&mut node);

                self.flush();

                node.wait();
            }

            return QLockGuard { lock: self };
        }
    }

    fn flush(&self) {
        unsafe {
            if self.lock.try_acquire() {
                let popped = self.stack.pop();
                if popped != dummy_node() {
                    (*popped).signal();
                    return;
                }

                self.lock.release();
            }
        }
    }
}

impl<'r> Drop for QLockGuard<'r> {
    fn drop(&mut self) {
        unsafe {
            let popped = self.lock.stack.pop();
            if popped != dummy_node() {
                (*popped).signal();
                return;
            }
        }

        self.lock.lock.release();

        self.lock.flush();
    }
}
