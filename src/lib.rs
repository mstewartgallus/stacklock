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

#[macro_use]
extern crate lazy_static;

mod backoff;
mod cacheline;
mod notifier;
mod exp;

use std::boxed::Box;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

use cacheline::CacheLineAligned;
use notifier::Notifier;

const ALLOCATE_NUM_LOOPS: usize = 100;
const ALLOCATE_MAX_LOG_NUM_PAUSES: usize = 7;

const DEALLOCATE_NUM_LOOPS: usize = 100;
const DEALLOCATE_MAX_LOG_NUM_PAUSES: usize = 7;

const SLEEP_NS: usize = 400;

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
        unsafe {
            let node = allocate_node();
            (*node).signal();
            QLock { head: CacheLineAligned::new(AtomicPtr::new(node)) }
        }
    }

    pub fn lock<'r>(&'r self) -> QLockGuard<'r> {
        unsafe {
            let node = get_local_node();

            let head = self.head.swap(node, Ordering::AcqRel);

            (*head).wait();

            set_local_node(head);

            QLockGuard {
                lock: PhantomData,
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
            (*self.node).signal();
        }
    }
}
thread_local! {
    static VALUE: RefCell<Option<NodeBox>> = RefCell::new(Some(NodeBox::new()));
}

fn get_local_node() -> *mut QLockNode {
    let mut value = None;
    VALUE.with(|x| mem::swap(&mut value, &mut *x.borrow_mut()));
    return NodeBox::into_raw(value.unwrap());
}

unsafe fn set_local_node(node: *mut QLockNode) {
    VALUE.with(|x| *x.borrow_mut() = Some(NodeBox::from_raw(node)));
}

struct NodeBox {
    node: *mut QLockNode,
}
impl NodeBox {
    fn new() -> Self {
        NodeBox { node: allocate_node() }
    }
    fn into_raw(mut self) -> *mut QLockNode {
        let mut x = ptr::null_mut();
        mem::swap(&mut self.node, &mut x);
        return x;
    }

    unsafe fn from_raw(node: *mut QLockNode) -> Self {
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
        (*head_ptr).notifier.reset();
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

struct QLockNode {
    notifier: Notifier,
    next: CacheLineAligned<AtomicPtr<QLockNode>>,
}

impl QLockNode {
    fn new() -> QLockNode {
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
