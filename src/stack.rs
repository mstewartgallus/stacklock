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

use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::thread;

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;
use notifier::Notifier;

const MAX_PUSH_EXP: usize = 6;
const PUSH_UNROLL: usize = 4;

pub struct Node {
    notifier: Notifier,
    next: CacheLineAligned<*mut Node>,
}

impl Node {
    #[inline(always)]
    pub fn new() -> Node {
        Node {
            notifier: Notifier::new(),
            next: CacheLineAligned::new(ptr::null_mut()),
        }
    }

    pub fn signal(&self) {
        self.notifier.signal();
    }

    pub fn wait(&self) {
        self.notifier.wait();
    }
}

pub struct Stack {
    head: CacheLineAligned<AtomicPtr<Node>>,
}

impl Stack {
    #[inline(always)]
    pub fn new() -> Self {
        Stack { head: CacheLineAligned::new(AtomicPtr::new(ptr::null_mut())) }
    }

    pub unsafe fn push(&self, node: *mut Node) {
        let mut head = self.head.load(Ordering::Relaxed);
        let mut counter = 0;
        loop {
            *(*node).next = head;
            match self.head
                .compare_exchange_weak(head, node, Ordering::Release, Ordering::Relaxed) {
                Err(newhead) => {
                    head = newhead;
                }
                Ok(_) => break,
            }
            let exp;
            if counter > MAX_PUSH_EXP {
                exp = 1 << MAX_PUSH_EXP;
            } else {
                exp = 1 << counter;
                counter += 1;
            }
            thread::yield_now();

            let spins = backoff::thread_num(1, exp);
            for _ in 0..spins % PUSH_UNROLL {
                backoff::pause();
            }

            for _ in 0..spins / PUSH_UNROLL {
                for _ in 0..PUSH_UNROLL {
                    backoff::pause();
                }
            }
        }
    }

    pub fn drain(&self) -> Stack {
        let head = self.head.swap(ptr::null_mut(), Ordering::AcqRel);
        Stack { head: CacheLineAligned::new(AtomicPtr::new(head)) }
    }

    pub fn reverse(self) -> Stack {
        unsafe {
            let p = self.head.load(Ordering::Acquire);
            let mut new = ptr::null_mut();
            let mut old = p;
            loop {
                if ptr::null_mut() == old {
                    break;
                }
                let node = old;
                old = *(*node).next;
                *(*node).next = new;
                new = node;
            }
            Stack { head: CacheLineAligned::new(AtomicPtr::new(new)) }
        }
    }

    pub fn pop(&mut self) -> *mut Node {
        unsafe {
            let head = self.head.load(Ordering::Acquire);
            if head == ptr::null_mut() {
                return ptr::null_mut();
            }

            let next = *(*head).next;

            self.head.store(next, Ordering::Release);

            return head;
        }
    }
}
