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
use libc;

use std::mem;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;

const LOOPS: usize = 30;

const TRIGGERED: u32 = 0;
const SPINNING: u32 = 1;
const WAITING: u32 = 2;

// Due to legacy issues on x86 operations on values smaller than 32
// bits can be slow.

/// A single waiter, single signaller event semaphore.  Signaled once
/// and then thrown away.
pub struct Notifier {
    state: CacheLineAligned<AtomicU32>,
}

const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl Notifier {
    pub fn new() -> Notifier {
        Notifier { state: CacheLineAligned::new(AtomicU32::new(SPINNING)) }
    }

    pub fn reset(&self) {
        self.state.store(SPINNING, Ordering::Release);
    }

    pub fn wait(&self) {
        'wait_loop: loop {
            {
                let mut counter = LOOPS;
                loop {
                    if self.state.load(Ordering::Relaxed) == TRIGGERED {
                        break 'wait_loop;
                    }
                    match counter.checked_sub(1) {
                        None => break,
                        Some(newcounter) => {
                            counter = newcounter;
                        }
                    }
                    backoff::pause();
                    thread::yield_now();
                }
            }

            if self.state
                .compare_exchange(SPINNING, WAITING, Ordering::AcqRel, Ordering::Relaxed)
                .is_err() {
                break;
            }

            let result: usize;
            unsafe {
                let trig: usize = mem::transmute(&self.state);
                result = syscall!(FUTEX, trig, FUTEX_WAIT_PRIVATE, WAITING, 0);
            }
            // woken up
            if 0 == result {
                break;
            }
            // futex checked and found that a trigger already happened
            if -libc::EWOULDBLOCK as usize == result {
                break;
            }

            if self.state
                .compare_exchange(WAITING, SPINNING, Ordering::Release, Ordering::Relaxed)
                .is_err() {
                break;
            }
        }
        atomic::fence(Ordering::Acquire);
    }

    pub fn signal(&self) {
        atomic::fence(Ordering::Release);

        if self.state.fetch_sub(1, Ordering::Relaxed) == 1 {
            return;
        }

        self.state.store(TRIGGERED, Ordering::Release);
        unsafe {
            let trig: usize = mem::transmute(&self.state);
            syscall!(FUTEX, trig, FUTEX_WAKE_PRIVATE, 1);
        }
    }
}
