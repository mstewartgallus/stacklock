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
#![feature(integer_atomics)]

#[macro_use]
extern crate syscall;

extern crate libc;

#[macro_use]
extern crate lazy_static;

extern crate qlock_util;

mod notifier;

use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::thread;

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;

use node::{QLockNode, NodeBox};

const HEAD_SPINS: usize = 60;

/// A CLH queue-lock
pub struct QLock {
    head: CacheLineAligned<AtomicPtr<QLockNode>>,
}
unsafe impl Send for QLock {}
unsafe impl Sync for QLock {}

pub struct QLockGuard<'r> {
    lock: &'r QLock,
    node: *mut QLockNode,
}

impl QLock {
    pub fn new() -> Self {
        QLock { head: CacheLineAligned::new(AtomicPtr::new(ptr::null_mut())) }
    }

    pub fn lock<'r>(&'r self) -> QLockGuard<'r> {
        unsafe {
            let node = NodeBox::into_raw(NodeBox::new());

            // This can't be avoided unless SeqCst orderings are used.
            // The issue is that we reset the notifier in a different
            // thread than this one.
            (*node).reset();
            let mut counter = HEAD_SPINS;
            let set_head;
            loop {
                if ptr::null_mut() == self.head.load(Ordering::Relaxed) {
                    if self.head
                        .compare_exchange_weak(ptr::null_mut(),
                                               node,
                                               Ordering::AcqRel,
                                               Ordering::Relaxed)
                        .is_ok() {
                        set_head = true;
                        break;
                    }
                }
                if 0 == counter {
                    set_head = false;
                    break;
                }
                backoff::pause();
                thread::yield_now();
                counter -= 1;
            }

            let head;
            if set_head {
                head = ptr::null_mut();
            } else {
                head = self.head.swap(node, Ordering::AcqRel);
                if head != ptr::null_mut() {
                    (*head).wait();
                }
            }

            NodeBox::from_raw(head);

            QLockGuard {
                lock: self,
                node: node,
            }
        }
    }
}
impl<'r> Drop for QLock {
    fn drop(&mut self) {
        unsafe {
            NodeBox::from_raw(self.head.load(Ordering::Acquire));
        }
    }
}

impl<'r> Drop for QLockGuard<'r> {
    fn drop(&mut self) {
        unsafe {
            let used_node;
            let actual_head = self.lock.head.load(Ordering::Relaxed);
            if actual_head == self.node {
                if self.lock
                    .head
                    .compare_exchange(self.node,
                                      ptr::null_mut(),
                                      Ordering::AcqRel,
                                      Ordering::Relaxed)
                    .is_ok() {
                    NodeBox::from_raw(self.node);
                    used_node = true;
                } else {
                    used_node = false;
                }
            } else {
                used_node = false;
            }

            if !used_node {
                (*self.node).signal();
            }
        }
    }
}

mod node {
    use std::boxed::Box;
    use std::mem;
    use std::ops::{Deref, DerefMut};
    use std::ptr;
    use std::sync::atomic;
    use std::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
    use std::thread;

    use libc;

    use qlock_util::backoff;
    use qlock_util::cacheline::CacheLineAligned;

    use notifier::Notifier;

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

        pub fn reset(&self) {
            self.notifier.reset();
        }

        pub fn signal(&self) {
            self.notifier.signal();
        }

        pub fn wait(&self) {
            self.notifier.wait();
        }
    }

    pub struct NodeBox {
        node: *mut QLockNode,
    }
    impl NodeBox {
        pub fn new() -> Self {
            unsafe {
                let list = libc::sched_getcpu() as usize % 2;
                let mut node = FREE_LIST[list].pop();
                if node == ptr::null_mut() {
                    node = Box::into_raw(Box::new(QLockNode::new()));
                }
                NodeBox { node: node }
            }
        }
        pub fn into_raw(mut self) -> *mut QLockNode {
            let mut x = ptr::null_mut();
            mem::swap(&mut self.node, &mut x);
            return x;
        }

        pub unsafe fn from_raw(node: *mut QLockNode) -> Self {
            NodeBox { node: node }
        }
    }
    impl Drop for NodeBox {
        fn drop(&mut self) {
            if self.node != ptr::null_mut() {
                unsafe {
                    let list = libc::sched_getcpu() as usize % 2;
                    FREE_LIST[list].push(self.node);
                }
            }
        }
    }

    lazy_static! {
        static ref FREE_LIST: [Stack; 2] = [Stack::new(), Stack::new()];
    }

    impl Deref for NodeBox {
        type Target = QLockNode;

        #[inline]
        fn deref(&self) -> &Self::Target {
            unsafe { self.node.as_ref().unwrap() }
        }
    }

    impl DerefMut for NodeBox {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { self.node.as_mut().unwrap() }
        }
    }

    unsafe fn from_tagged(tagged: u64) -> (*mut QLockNode, u32) {
        let ptr_bits = (tagged >> 22) << 6;
        let ptr = mem::transmute(ptr_bits);
        let tag = tagged & ((1 << 22) - 1);
        return (ptr, tag as u32);
    }

    unsafe fn to_tagged(ptr: *mut QLockNode, mut tag: u32) -> u64 {
        tag = tag & ((1 << 22) - 1);
        let mut ptr_bits: u64 = mem::transmute(ptr);
        ptr_bits = ptr_bits >> 6;
        return ptr_bits << 22 | tag as u64;
    }

    pub struct Stack {
        head: CacheLineAligned<AtomicU64>,
    }
    impl Stack {
        pub fn new() -> Stack {
            Stack { head: CacheLineAligned::new(AtomicU64::new(0)) }
        }

        pub unsafe fn pop(&self) -> *mut QLockNode {
            atomic::fence(Ordering::Release);

            let mut list = self.head.load(Ordering::Acquire);
            let (mut head_ptr, mut head_tag) = from_tagged(list);
            if head_ptr == ptr::null_mut() {
                return ptr::null_mut();
            }

            loop {
                atomic::fence(Ordering::Acquire);
                let next = (*head_ptr).next.load(Ordering::Acquire);

                let to_replace = to_tagged(next, head_tag + 1);
                let maybe_list = self.head.load(Ordering::Relaxed);
                if maybe_list == list {
                    match self.head.compare_exchange_weak(list,
                                                          to_replace,
                                                          Ordering::Release,
                                                          Ordering::Relaxed) {
                        Err(newlist) => {
                            list = newlist;
                            let (a, b) = from_tagged(list);
                            head_ptr = a;
                            head_tag = b;
                            if head_ptr == ptr::null_mut() {
                                return ptr::null_mut();
                            }
                        }
                        Ok(_) => {
                            break;
                        }
                    }
                } else {
                    list = maybe_list;
                    let (a, b) = from_tagged(list);
                    head_ptr = a;
                    head_tag = b;
                    if head_ptr == ptr::null_mut() {
                        return ptr::null_mut();
                    }
                }
                backoff::pause();
                thread::yield_now();
            }
            (*head_ptr).next.store(ptr::null_mut(), Ordering::Relaxed);
            return head_ptr;
        }

        pub unsafe fn push(&self, node: *mut QLockNode) {
            let mut list = self.head.load(Ordering::Relaxed);
            let (mut head_ptr, mut head_tag) = from_tagged(list);
            loop {
                (*node).next.store(head_ptr, Ordering::Relaxed);

                match self.head.compare_exchange_weak(list,
                                                      to_tagged(node, head_tag + 1),
                                                      Ordering::Release,
                                                      Ordering::Relaxed) {
                    Err(newlist) => {
                        list = newlist;
                        let (a, b) = from_tagged(list);
                        head_ptr = a;
                        head_tag = b;
                    }
                    Ok(_) => {
                        break;
                    }
                }
                backoff::pause();
                thread::yield_now();
            }
        }
    }


    #[cfg(test)]
    mod test {
        use super::{NodeBox, to_tagged, from_tagged};

        #[test]
        fn test() {
            unsafe {
                let a = NodeBox::into_raw(NodeBox::new());
                let b = 40902;

                let (maybe_a, maybe_b) = from_tagged(to_tagged(a, b));

                assert_eq!(a, maybe_a);
                assert_eq!(b, maybe_b);

                NodeBox::from_raw(a);
            }
            unsafe {
                let input = u64::max_value();
                let (a, b) = from_tagged(input);
                let output = to_tagged(a, b);
                assert_eq!(input, output);
            }
        }
    }
}
