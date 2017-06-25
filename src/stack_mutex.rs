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
use std::sync::atomic;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use dontshare::DontShare;
use sleepfast;
use weakrand;

use notifier::Notifier;

const MAX_EXP: usize = 8;

/// A queue lock like the CLH or MCS ones but that use a stack
/// instead.  This algorithm is a bit hairy but is a fairly straight
/// forward translation of the TLA+ specification under
/// tla/StackLock.tla to use weak compare and swap and a Treiber
/// Stack.
pub struct RawMutex {
    head: AtomicAba,
}
unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

pub struct RawMutexGuard<'r> {
    lock: &'r RawMutex,
}

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { head: AtomicAba::new(Aba::new(ptr::null_mut(), 0, false)) }
    }

    pub fn lock<'r>(&'r self) -> RawMutexGuard<'r> {
        let mut node = Node::new();

        let mut head = self.head.load(Ordering::Relaxed);
        let mut counter = 0;
        loop {
            if head.locked() {
                // On a locked stack push the node
                *node.next = head.ptr();
                let new = Aba::new(&mut node, head.tag().wrapping_add(1), true);

                if let Err(newhead) = self.head
                    .compare_exchange_weak(head, new, Ordering::SeqCst, Ordering::Relaxed) {
                    head = newhead;
                } else {
                    break;
                }
            } else {
                // Acquire an unlocked stack
                let new = Aba::new(head.ptr(), head.tag().wrapping_add(1), true);

                if let Err(newhead) = self.head
                    .compare_exchange_weak(head, new, Ordering::SeqCst, Ordering::Relaxed) {
                    head = newhead;
                } else {
                    return RawMutexGuard { lock: self };
                }
            }

            thread::yield_now();

            let exp = if counter < MAX_EXP {
                let old = counter;
                counter = counter.wrapping_add(1);
                1 << old
            } else {
                1 << MAX_EXP
            };
            let spins = weakrand::rand(1, exp);

            sleepfast::pause_times(spins as usize);
        }

        node.wait();
        return RawMutexGuard { lock: self };
    }
}
impl<'r> Drop for RawMutexGuard<'r> {
    fn drop(&mut self) {
        unsafe {
            let mut head = self.lock.head.load(Ordering::Relaxed);
            assert!(head.locked());

            let mut counter = 0;
            loop {
                if ptr::null_mut() == head.ptr() {
                    // Release the lock on an empty stack
                    let new = Aba::new(ptr::null_mut(), head.tag().wrapping_add(1), false);
                    if let Err(newhead) = self.lock
                        .head
                        .compare_exchange_weak(head, new, Ordering::SeqCst, Ordering::Relaxed) {
                        head = newhead;
                    } else {
                        break;
                    }
                } else {
                    // Pop off a nonempty stack and pass off the lock
                    atomic::fence(Ordering::Acquire);
                    let next;
                    {
                        let head_ref = &mut *head.ptr();
                        next = *head_ref.next;
                    }
                    let new = Aba::new(next, head.tag().wrapping_add(1), true);
                    if let Err(newhead) = self.lock
                        .head
                        .compare_exchange_weak(head, new, Ordering::SeqCst, Ordering::Relaxed) {
                        head = newhead;
                    } else {
                        (*head.ptr()).signal();
                        break;
                    }
                }
                assert!(head.locked());

                thread::yield_now();

                let exp = if counter < MAX_EXP {
                    let old = counter;
                    counter = counter.wrapping_add(1);
                    1 << old
                } else {
                    1 << MAX_EXP
                };
                let spins = weakrand::rand(1, exp);

                sleepfast::pause_times(spins as usize);
            }
        }
    }
}

struct Node {
    notifier: Notifier,
    next: DontShare<*mut Node>,
}

impl Node {
    #[inline(always)]
    fn new() -> Node {
        Node {
            notifier: Notifier::new(),
            next: DontShare::new(ptr::null_mut()),
        }
    }

    fn signal(&self) {
        self.notifier.signal();
    }

    fn wait(&self) {
        self.notifier.wait();
    }
}

#[derive(Copy, Clone)]
struct Aba {
    ptr: u64,
}

// Because of pointer alignment to 128 bytes 7 end bits are always zero.
const ZERO_BITS: u64 = 7;

const LOCKED_OFFSET: u64 = 0;
const LOCKED_SIZE: u64 = 1;

const TAG_OFFSET: u64 = LOCKED_SIZE;
const TAG_SIZE: u64 = 22;

const PTR_OFFSET: u64 = LOCKED_SIZE + TAG_SIZE;
const PTR_SIZE: u64 = 41;

impl Aba {
    #[inline(always)]
    fn new(node: *mut Node, tag: u32, locked: bool) -> Self {
        unsafe {
            let lock_bit: u64 = if locked { 1 } else { 0 };
            let node_bits: u64 = mem::transmute(node);
            let tag_bits: u64 = (tag & ((1 << TAG_SIZE) - 1)) as u64;
            Aba {
                ptr: lock_bit << LOCKED_OFFSET | tag_bits << TAG_OFFSET |
                     (node_bits >> ZERO_BITS) << PTR_OFFSET,
            }
        }
    }

    fn get(&self, offset: u64, size: u64) -> u64 {
        (self.ptr >> offset) & ((1 << size) - 1)
    }

    fn locked(&self) -> bool {
        self.get(LOCKED_OFFSET, LOCKED_SIZE) != 0
    }

    fn ptr(&self) -> *mut Node {
        unsafe {
            let node_bits = self.get(PTR_OFFSET, PTR_SIZE) << ZERO_BITS;
            mem::transmute(node_bits)
        }
    }
    fn tag(&self) -> u32 {
        let tag_bits = self.get(TAG_OFFSET, TAG_SIZE);
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
        let mut dblcheck = self.ptr.load(fail);
        if dblcheck == old.ptr {
            match self.ptr
                .compare_exchange_weak(old.ptr, new.ptr, success, fail) {
                Err(x) => dblcheck = x,
                Ok(x) => return Ok(Aba { ptr: x }),
            }
        }
        return Err(Aba { ptr: dblcheck });
    }
}
