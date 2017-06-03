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
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;
use notifier::Notifier;

struct AtomicAba {
    ptr: AtomicU64,
}
impl AtomicAba {
    #[inline(always)]
    fn new() -> Self {
        AtomicAba { ptr: AtomicU64::new(0) }
    }

    fn load(&self, ordering: Ordering) -> (*mut Node, u32) {
        from_u64(self.ptr.load(ordering))
    }

    fn compare_exchange_weak(&self,
                             old: (*mut Node, u32),
                             new: (*mut Node, u32),
                             success: Ordering,
                             fail: Ordering)
                             -> Result<(*mut Node, u32), (*mut Node, u32)> {
        match self.ptr
            .compare_exchange_weak(to_u64(old.0, old.1), to_u64(new.0, new.1), success, fail) {
            Err(x) => Err(from_u64(x)),
            Ok(x) => Ok(from_u64(x)),
        }
    }
}

fn to_u64(node: *mut Node, tag: u32) -> u64 {
    unsafe {
        let node_bits: u64 = mem::transmute(node);
        let tag_bits: u64 = (tag & ((1 << 23) - 1)) as u64;
        tag_bits | node_bits << 16
    }
}
fn from_u64(ptr: u64) -> (*mut Node, u32) {
    unsafe {
        let node_bits = (ptr >> 23) << 7;
        let tag_bits: u64 = ptr & ((1 << 23) - 1);
        (mem::transmute(node_bits), tag_bits as u32)
    }
}

const MAX_EXP: usize = 6;

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
    head: CacheLineAligned<AtomicAba>,
}

impl Stack {
    #[inline(always)]
    pub fn new() -> Self {
        Stack { head: CacheLineAligned::new(AtomicAba::new()) }
    }

    pub unsafe fn push(&self, node: *mut Node) {
        let mut head = self.head.load(Ordering::Relaxed);
        let mut counter = 0;
        loop {
            let new = (node, head.1.wrapping_add(1));

            *(*node).next = head.0;

            let newhead = self.head.load(Ordering::Relaxed);
            if newhead != head {
                head = newhead;
            } else {
                match self.head
                    .compare_exchange_weak(head, new, Ordering::Release, Ordering::Relaxed) {
                    Err(newhead) => {
                        head = newhead;
                    }
                    Ok(_) => break,
                }
            }

            let exp;
            if counter > MAX_EXP {
                exp = 1 << MAX_EXP;
            } else {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            }
            backoff::yield_now();

            let spins = backoff::thread_num(1, exp);

            backoff::pause_times(spins);
        }
    }

    pub fn pop(&self) -> *mut Node {
        unsafe {
            let mut head = self.head.load(Ordering::Relaxed);
            if head.0 == ptr::null_mut() {
                return ptr::null_mut();
            }

            let mut counter = 0;
            loop {
                let next = *(*head.0).next;
                let new = (next, head.1.wrapping_add(1));

                match self.head
                    .compare_exchange_weak(head, new, Ordering::Release, Ordering::Relaxed) {
                    Err(newhead) => {
                        head = newhead;
                        if head.0 == ptr::null_mut() {
                            return ptr::null_mut();
                        }
                    }
                    Ok(_) => break,
                }

                let exp;
                if counter > MAX_EXP {
                    exp = 1 << MAX_EXP;
                } else {
                    exp = 1 << counter;
                    counter = counter.wrapping_add(1);
                }
                backoff::yield_now();

                let spins = backoff::thread_num(1, exp);

                backoff::pause_times(spins);
            }
            return head.0;
        }
    }
}
