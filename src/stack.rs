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
use std::mem;
use std::sync::atomic;
use std::sync::atomic::{AtomicU64, AtomicPtr, Ordering};
use std::thread;

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;
use notifier::Notifier;

const MAX_PUSH_EXP: usize = 6;
const MAX_POP_EXP: usize = 6;
const PUSH_UNROLL: usize = 4;
const POP_UNROLL: usize = 4;

struct Aba {
    ptr: AtomicU64,
}
impl Aba {
    #[inline(always)]
    fn new() -> Aba {
        Aba { ptr: AtomicU64::new(0) }
    }

    fn load(&self, ordering: Ordering) -> (*mut Node, u32) {
        return from_u64(self.ptr.load(ordering));
    }

    fn compare_exchange_weak(&self,
                             old: (*mut Node, u32),
                             new: (*mut Node, u32),
                             success: Ordering,
                             fail: Ordering)
                             -> Result<(*mut Node, u32), (*mut Node, u32)> {
        let old_num = to_u64(old.0, old.1);
        let new_num = to_u64(new.0, new.1);
        match self.ptr.compare_exchange_weak(old_num, new_num, success, fail) {
            Ok(x) => Ok(from_u64(x)),
            Err(x) => Err(from_u64(x)),
        }
    }
}

fn to_u64(ptr: *mut Node, tag: u32) -> u64 {
    unsafe {
        let ptr_val: u64 = mem::transmute(ptr);
        let tag_val: u64 = (tag & ((1 << 23) - 1)) as u64;
        return ptr_val << 16 | tag_val;
    }
}

fn from_u64(num: u64) -> (*mut Node, u32) {
    unsafe {
        let ptr: *mut Node = mem::transmute((num & !((1 << 23) - 1)) >> 16);
        let tag: u32 = (num & ((1 << 23) - 1)) as u32;
        return (ptr, tag);
    }
}

pub struct Node {
    notifier: Notifier,
    next: CacheLineAligned<AtomicPtr<Node>>,
}

impl Node {
    #[inline(always)]
    pub fn new() -> Node {
        Node {
            notifier: Notifier::new(),
            next: CacheLineAligned::new(AtomicPtr::new(ptr::null_mut())),
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
    head: CacheLineAligned<Aba>,
}

impl Stack {
    #[inline(always)]
    pub fn new() -> Self {
        Stack { head: CacheLineAligned::new(Aba::new()) }
    }

    pub unsafe fn push(&self, node: *mut Node) {
        let mut head = self.head.load(Ordering::Relaxed);
        let mut counter = 0;
        loop {
            (*node).next.store(head.0, Ordering::Relaxed);
            match self.head.compare_exchange_weak(head,
                                                  (node, head.1.wrapping_add(1)),
                                                  Ordering::Release,
                                                  Ordering::Relaxed) {
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

    pub fn pop(&self) -> *mut Node {
        unsafe {
            let mut head = self.head.load(Ordering::Relaxed);
            if head.0 == ptr::null_mut() {
                return ptr::null_mut();
            }

            let mut counter = 0;
            loop {
                atomic::fence(Ordering::Acquire);
                let next = (*head.0).next.load(Ordering::Relaxed);
                match self.head
                    .compare_exchange_weak(head,
                                           (next, head.1.wrapping_add(1)),
                                           Ordering::Acquire,
                                           Ordering::Relaxed) {
                    Err(newhead) => {
                        head = newhead;
                        if head.0 == ptr::null_mut() {
                            return ptr::null_mut();
                        }
                    }
                    Ok(_) => return head.0,
                }
                let exp;
                if counter > MAX_POP_EXP {
                    exp = 1 << MAX_POP_EXP;
                } else {
                    exp = 1 << counter;
                    counter += 1;
                }
                thread::yield_now();

                let spins = backoff::thread_num(1, exp);
                for _ in 0..spins % POP_UNROLL {
                    backoff::pause();
                }

                for _ in 0..spins / POP_UNROLL {
                    for _ in 0..POP_UNROLL {
                        backoff::pause();
                    }
                }
            }
        }
    }
}
