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
use std::cmp;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;
use notifier::Notifier;

static mut DUMMY_NODE: Node = Node::new_uninit();

#[inline]
pub fn dummy_node() -> *mut Node {
    unsafe {
        return &mut DUMMY_NODE;
    }
}

#[derive(Copy, Clone)]
struct Aba {
    ptr: u64,
}

impl Aba {
    #[inline(always)]
    fn new(node: *mut Node, tag: u32) -> Self {
        unsafe {
            let node_bits: u64 = mem::transmute(node);
            let tag_bits: u64 = (tag & ((1 << 23) - 1)) as u64;
            Aba { ptr: tag_bits | node_bits << 16 }
        }
    }
    fn ptr(&self) -> *mut Node {
        unsafe {
            let node_bits = (self.ptr >> 23) << 7;
            mem::transmute(node_bits)
        }
    }
    fn tag(&self) -> u32 {
        let tag_bits: u64 = self.ptr & ((1 << 23) - 1);
        tag_bits as u32
    }
}
impl PartialEq for Aba {
    fn eq(&self, other: &Aba) -> bool {
        self.ptr == other.ptr
    }
}
struct AtomicAba {
    ptr: AtomicU64,
}
impl AtomicAba {
    #[inline(always)]
    fn new(ptr: Aba) -> Self {
        AtomicAba { ptr: AtomicU64::new(ptr.ptr) }
    }

    fn load(&self, ordering: Ordering) -> Aba {
        Aba { ptr: self.ptr.load(ordering) }
    }

    fn compare_exchange_weak(&self,
                             old: Aba,
                             new: Aba,
                             success: Ordering,
                             fail: Ordering)
                             -> Result<Aba, Aba> {
        // Test and test and set optimization
        let dblcheck = self.ptr.load(fail);
        if dblcheck != old.ptr {
            return Err(Aba { ptr: dblcheck });
        }
        match self.ptr
            .compare_exchange_weak(old.ptr, new.ptr, success, fail) {
            Err(x) => Err(Aba { ptr: x }),
            Ok(x) => Ok(Aba { ptr: x }),
        }
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
            next: CacheLineAligned::new(dummy_node()),
        }
    }

    pub const fn new_uninit() -> Node {
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
        Stack { head: CacheLineAligned::new(AtomicAba::new(Aba::new(dummy_node(), 0))) }
    }

    pub unsafe fn push(&self, node: *mut Node) {
        let mut head = self.head.load(Ordering::Relaxed);

        let mut new = Aba::new(node, head.tag().wrapping_add(1));
        *(*node).next = head.ptr();

        let mut counter = 0;
        loop {
            match self.head
                .compare_exchange_weak(head, new, Ordering::Release, Ordering::Relaxed) {
                Err(newhead) => {
                    head = newhead;
                    new = Aba::new(node, head.tag().wrapping_add(1));
                    *(*node).next = head.ptr();
                }
                Ok(_) => break,
            }

            backoff::yield_now();

            let exp = cmp::min(counter, MAX_EXP);
            if counter < MAX_EXP {
                counter = counter.wrapping_add(1);
            }
            let spins = backoff::thread_num(1, 1 << exp);

            backoff::pause_times(spins);
        }
    }

    pub fn pop(&self) -> *mut Node {
        unsafe {
            let mut head = self.head.load(Ordering::Relaxed);
            let mut next;
            let mut new;

            {
                let head_ptr = head.ptr();

                next = *(*head_ptr).next;
                new = Aba::new(next, head.tag().wrapping_add(1));

                if head_ptr == dummy_node() {
                    return dummy_node();
                }
            }

            let mut counter = 0;
            loop {
                match self.head
                    .compare_exchange_weak(head, new, Ordering::Release, Ordering::Relaxed) {
                    Err(newhead) => {
                        head = newhead;

                        {
                            let head_ptr = head.ptr();

                            next = *(*head_ptr).next;
                            new = Aba::new(next, head.tag().wrapping_add(1));

                            if head_ptr == dummy_node() {
                                return dummy_node();
                            }
                        }
                    }
                    Ok(_) => break,
                }

                backoff::yield_now();


                let exp = cmp::min(counter, MAX_EXP);
                if counter < MAX_EXP {
                    counter = counter.wrapping_add(1);
                }
                let spins = backoff::thread_num(1, 1 << exp);

                backoff::pause_times(spins);
            }
            return head.ptr();
        }
    }
}
