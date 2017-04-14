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
#![feature(integer_atomics, asm, repr_simd, attr_literals)]

#[macro_use]
extern crate syscall;
extern crate libc;
extern crate rand;

mod backoff;
mod cacheline;
mod notifier;
mod exp;

use std::sync::atomic;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::time::Duration;
use std::thread;
use std::ptr;

use cacheline::CacheLineAligned;
use notifier::Notifier;

const RELEASE_NUM_LOOPS: usize = 10;
const RELEASE_MAX_LOG_NUM_PAUSES: usize = 7;

const SLEEP_NS: usize = 200;

/// An MCS queue-lock
pub struct QLock {
    head: CacheLineAligned<AtomicPtr<QLockNode>>,
}
unsafe impl Send for QLock {}
unsafe impl Sync for QLock {}

pub struct QLockGuard<'r> {
    lock: &'r QLock,
    node: &'r mut QLockNode,
}

impl QLock {
    pub fn new() -> Self {
        QLock { head: CacheLineAligned::new(AtomicPtr::new(ptr::null_mut())) }
    }

    pub fn lock<'r>(&'r self, node: &'r mut QLockNode) -> QLockGuard<'r> {
        node.notifier.reset();
        node.next.store(ptr::null_mut(), Ordering::Relaxed);

        atomic::fence(Ordering::Release);

        if let Err(_) = self.head
            .compare_exchange_weak(ptr::null_mut(), node, Ordering::Relaxed, Ordering::Relaxed) {
            let head = self.head.swap(node, Ordering::Relaxed);
            if head != ptr::null_mut() {
                unsafe {
                    atomic::fence(Ordering::Acquire);
                    (*head).next.store(node, Ordering::Release);
                    node.wait();
                }
            }
        }

        atomic::fence(Ordering::Acquire);

        QLockGuard {
            lock: self,
            node: node,
        }
    }
}
impl<'r> Drop for QLockGuard<'r> {
    fn drop(&mut self) {
        unsafe {
            atomic::fence(Ordering::Release);

            let mut next = self.node.next.load(Ordering::Relaxed);
            if ptr::null_mut() == next {
                if let Ok(_) = self.lock.head.compare_exchange(self.node,
                                                               ptr::null_mut(),
                                                               Ordering::Relaxed,
                                                               Ordering::Relaxed) {
                    return;
                }

                let mut counter = 0;
                loop {
                    next = self.node.next.load(Ordering::Relaxed);
                    if next != ptr::null_mut() {
                        break;
                    }
                    if counter >= RELEASE_NUM_LOOPS {
                        break;
                    }

                    for _ in 0..backoff::thread_num(exp::exp(counter,
                                                             RELEASE_NUM_LOOPS,
                                                             RELEASE_MAX_LOG_NUM_PAUSES)) {
                        backoff::pause();
                    }
                    counter += 1;
                }
                if next == ptr::null_mut() {
                    loop {
                        next = self.node.next.load(Ordering::Relaxed);
                        if next != ptr::null_mut() {
                            break;
                        }
                        thread::sleep(Duration::new(0, backoff::thread_num(SLEEP_NS) as u32));
                    }
                }
            }

            (*next).signal();
        }
    }
}

pub struct QLockNode {
    notifier: Notifier,
    next: CacheLineAligned<AtomicPtr<QLockNode>>,
}

impl QLockNode {
    pub fn new() -> QLockNode {
        QLockNode {
            notifier: Notifier::new(),
            next: CacheLineAligned::new(AtomicPtr::new(ptr::null_mut())),
        }
    }

    fn signal(&self) {
        self.notifier.signal();
    }

    fn wait(&self) {
        self.notifier.wait();
    }
}
