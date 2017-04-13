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

use std::thread;
use std::mem;
use std::sync::atomic;
use std::sync::atomic::{AtomicU64, Ordering};

use exp;
use backoff;
use cacheline::CacheLineAligned;

const TOTAL_SPINS: usize = 40;
const PERCENT_YIELD: usize = 50;
const MAX_PAUSE_LENGTH: usize = 9;
const NUM_PAUSE_SPINS: usize = (TOTAL_SPINS * (100 - PERCENT_YIELD)) / 100;
const NUM_YIELD_SPINS: usize = (TOTAL_SPINS * PERCENT_YIELD) / 100;

const SPINNING: u64 = 0;
const NOT_SPINNING: u64 = 1;

/// A single waiter, single signaller event semaphore.  Signaled once
/// and then thrown away.
pub struct Notifier {
    spin_state: CacheLineAligned<AtomicU64>,
    triggered: CacheLineAligned<AtomicU64>,
}

const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

fn untriggered() -> u64 {
    u64::max_value()
}
// Make sure comparisons are against zero
fn triggered() -> u64 {
    0
}

impl Notifier {
    pub fn new() -> Notifier {
        Notifier {
            spin_state: CacheLineAligned::new(AtomicU64::new(SPINNING)),
            triggered: CacheLineAligned::new(AtomicU64::new(untriggered())),
        }
    }

    pub fn reset(&self) {
        self.spin_state.store(SPINNING, Ordering::Relaxed);
        self.triggered.store(untriggered(), Ordering::Relaxed);
    }

    pub fn wait(&self) {
        'wait_loop: loop {
            {
                let mut counter = 0;
                loop {
                    if triggered() == self.triggered.load(Ordering::Relaxed) {
                        break 'wait_loop;
                    }
                    if counter >= NUM_PAUSE_SPINS {
                        break;
                    }
                    for _ in 0..exp::exp(counter, NUM_PAUSE_SPINS, MAX_PAUSE_LENGTH) {
                        backoff::pause();
                    }
                    counter += 1;
                }
            }

            // For some reason, falling back to yielding to another
            // thread is faster after a certain point.
            {
                let mut ii = NUM_YIELD_SPINS;
                loop {
                    if triggered() == self.triggered.load(Ordering::Relaxed) {
                        break 'wait_loop;
                    }
                    ii = ii - 1;
                    if 0 == ii {
                        break;
                    }
                    thread::yield_now();
                }
            }

            self.spin_state.store(NOT_SPINNING, Ordering::Relaxed);

            atomic::fence(Ordering::AcqRel);

            if triggered() == self.triggered.load(Ordering::Relaxed) {
                break;
            }

            // We make sure that both 32 bit chunks change on store so
            // this is okay on both little endian and big endian.
            let result: usize;
            unsafe {
                let trig: usize = mem::transmute(&self.triggered);
                result = syscall!(FUTEX, trig, FUTEX_WAIT_PRIVATE, untriggered(), 0);
            }
            // woken up
            if 0 == result {
                break;
            }
            // futex checked and found that a trigger already happened
            if -libc::EWOULDBLOCK as usize == result {
                break;
            }

            self.spin_state.store(SPINNING, Ordering::Relaxed);
        }
        atomic::fence(Ordering::Acquire);
    }

    pub fn signal(&self) {
        // If the waiter was spinning we can avoid a syscall.
        atomic::fence(Ordering::Release);

        self.triggered.store(triggered(), Ordering::Relaxed);

        atomic::fence(Ordering::AcqRel);

        if SPINNING == self.spin_state.load(Ordering::Relaxed) {
            return;
        }

        unsafe {
            let trig: usize = mem::transmute(&self.triggered);
            syscall!(FUTEX, trig, FUTEX_WAKE_PRIVATE, 1);
        }
    }
}
