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
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;
use sleepfast;
use weakrand;

const INITIAL_LOOPS: usize = 20;
const NUM_LOOPS: usize = 20;
const MAX_EXP: usize = 8;

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const LOCKED_WITH_WAITER: u32 = 2;

/// This is basically Ulrich-Drepper's futexes are tricky futex lock
pub struct RawMutex {
    val: AtomicU32,
}
const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> RawMutex {
        RawMutex { val: AtomicU32::new(UNLOCKED) }
    }

    pub fn try_lock(&self) -> bool {
        if self.val.load(Ordering::Relaxed) != UNLOCKED {
            return false;
        }

        if self.val
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok() {
            return true;
        }
        return false;
    }

    pub fn lock(&self) {
        {
            let mut counter = 0;
            loop {
                if self.try_lock() {
                    return;
                }

                if counter > INITIAL_LOOPS {
                    break;
                }

                thread::yield_now();

                let exp = if counter < MAX_EXP {
                    1 << counter
                } else {
                    1 << MAX_EXP
                };

                counter = counter.wrapping_add(1);

                let spins = weakrand::rand(1, exp);

                sleepfast::pause_times(spins as usize);
            }
        }

        if self.val.load(Ordering::Relaxed) != LOCKED_WITH_WAITER {
            if UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
                return;
            }
        }

        'big_loop: loop {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAIT_PRIVATE, LOCKED_WITH_WAITER, 0);
            }

            let mut counter = 0;
            loop {
                if self.val.load(Ordering::Relaxed) != LOCKED_WITH_WAITER {
                    if UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
                        break 'big_loop;
                    }
                }

                if counter > NUM_LOOPS {
                    break;
                }

                thread::yield_now();

                let exp = if counter < MAX_EXP {
                    1 << counter
                } else {
                    1 << MAX_EXP
                };

                counter = counter.wrapping_add(1);

                let spins = weakrand::rand(1, exp);

                sleepfast::pause_times(spins as usize);
            }
        }
    }

    pub fn unlock(&self) {
        if self.val.swap(UNLOCKED, Ordering::SeqCst) == LOCKED_WITH_WAITER {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAKE_PRIVATE, 1);
            }
        }
    }
}
