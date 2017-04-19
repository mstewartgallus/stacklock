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

use std::cell::RefCell;
use std::marker::PhantomData;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

use qlock_util::cacheline::CacheLineAligned;

use node::{QLockNode, NodeBox};

/// A CLH queue-lock
pub struct QLock {
    head: CacheLineAligned<AtomicPtr<QLockNode>>,
}
unsafe impl Send for QLock {}
unsafe impl Sync for QLock {}

pub struct QLockGuard<'r> {
    lock: PhantomData<&'r QLock>,
    node: *mut QLockNode,
}

impl QLock {
    pub fn new() -> Self {
        let node = NodeBox::new();
        (*node).signal();
        QLock { head: CacheLineAligned::new(AtomicPtr::new(NodeBox::into_raw(node))) }
    }

    pub fn lock<'r>(&'r self) -> QLockGuard<'r> {
        LOCAL_NODE_STASH.with(|node_store| unsafe {
            let node = NodeBox::into_raw(ptr::read(&*node_store.borrow_mut()));

            // This can't be avoided unless SeqCst orderings are used.
            // The issue is that we reset the notifier in a different
            // thread than this one.
            (*node).reset();
            let head = self.head.swap(node, Ordering::AcqRel);

            (*head).wait();

            ptr::write(&mut *node_store.borrow_mut(), NodeBox::from_raw(head));

            QLockGuard {
                lock: PhantomData,
                node: node,
            }
        })
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
            (*self.node).signal();
        }
    }
}

thread_local! {
    static LOCAL_NODE_STASH: RefCell<NodeBox> = RefCell::new(NodeBox::new());
}

mod node {
    use std::boxed::Box;
    use std::mem;
    use std::ptr;
    use std::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
    use std::thread;
    use std::time::Duration;
    use std::ops::{Deref, DerefMut};

    use qlock_util::cacheline::CacheLineAligned;
    use qlock_util::backoff;
    use qlock_util::exp;
    use notifier::Notifier;

    const ALLOCATE_NUM_LOOPS: usize = 100;
    const ALLOCATE_MAX_LOG_NUM_PAUSES: usize = 7;

    const DEALLOCATE_NUM_LOOPS: usize = 100;
    const DEALLOCATE_MAX_LOG_NUM_PAUSES: usize = 7;

    const SLEEP_NS: usize = 400;

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
            NodeBox { node: allocate_node() }
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
                    deallocate_node(self.node);
                }
            }
        }
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
        let ptr = mem::transmute((tagged & ((1 << 42) - 1)) << 6);
        let tag = (tagged >> 42) as u32;
        return (ptr, tag);
    }

    unsafe fn to_tagged(ptr: *mut QLockNode, tag: u32) -> u64 {
        let mut ptr_bits: u64 = mem::transmute(ptr);
        ptr_bits = ptr_bits >> 6;
        return ptr_bits | (tag as u64) << 42;
    }

    lazy_static! {
        static ref FREE_LIST: AtomicU64 = AtomicU64::new(0);
    }

    fn allocate_node() -> *mut QLockNode {
        unsafe {
            let free_list = &FREE_LIST;

            let mut list = free_list.load(Ordering::Acquire);
            let mut counter = 0;
            loop {
                let (head_ptr, head_tag) = from_tagged(list);
                if head_ptr == ptr::null_mut() {
                    let boxed = Box::new(QLockNode::new());
                    return Box::into_raw(boxed);
                }

                let next = (*head_ptr).next.load(Ordering::Acquire);
                match free_list.compare_exchange_weak(list,
                                                      to_tagged(next, head_tag + 1),
                                                      Ordering::AcqRel,
                                                      Ordering::Acquire) {
                    Err(newlist) => {
                        list = newlist;
                    }
                    Ok(_) => {
                        break;
                    }
                }
                if counter < ALLOCATE_NUM_LOOPS {
                    for _ in 0..backoff::thread_num(exp::exp(counter,
                                                             ALLOCATE_NUM_LOOPS,
                                                             ALLOCATE_MAX_LOG_NUM_PAUSES)) {
                        backoff::pause();
                    }
                    counter += 1;
                } else {
                    thread::sleep(Duration::new(0, backoff::thread_num(SLEEP_NS) as u32));
                }
            }
            let (head_ptr, _) = from_tagged(list);
            (*head_ptr).next.store(ptr::null_mut(), Ordering::Relaxed);
            return head_ptr;
        }
    }

    unsafe fn deallocate_node(node: *mut QLockNode) {
        let free_list = &FREE_LIST;

        let mut list = free_list.load(Ordering::Acquire);
        let mut counter = 0;
        loop {
            let (head_ptr, head_tag) = from_tagged(list);

            (*node).next.store(head_ptr, Ordering::Release);

            match free_list.compare_exchange_weak(list,
                                                  to_tagged(node, head_tag + 1),
                                                  Ordering::AcqRel,
                                                  Ordering::Acquire) {
                Err(newlist) => {
                    list = newlist;
                }
                Ok(_) => {
                    break;
                }
            }
            if counter < DEALLOCATE_NUM_LOOPS {
                for _ in 0..backoff::thread_num(exp::exp(counter,
                                                         DEALLOCATE_NUM_LOOPS,
                                                         DEALLOCATE_MAX_LOG_NUM_PAUSES)) {
                    backoff::pause();
                }
                counter += 1;
            } else {
                thread::sleep(Duration::new(0, backoff::thread_num(SLEEP_NS) as u32));
            }
        }
    }
}
