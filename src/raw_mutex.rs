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
use libc;
use dontshare::DontShare;
use weakrand;
use sleepfast;

use stack_mutex;
use tts_mutex;

use std::thread;

const NUM_FALLBACK: usize = 2;
const MAX_EXP: usize = 8;
const LOOPS: usize = 10;

// A simple test-and test and set lock causes lots of intercore
// commmunication when contended by lots of threads.  A StackMutex has
// a bunch of overhead.  Use a test-and-test and set lock that falls
// back to separate StackMutexs under heavy contention.
pub struct RawMutex {
    spin_mutex: DontShare<tts_mutex::RawMutex>,
    fallback: [DontShare<stack_mutex::RawMutex>; NUM_FALLBACK],
}
unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex {
            spin_mutex: DontShare::new(tts_mutex::RawMutex::new()),
            fallback: [DontShare::new(stack_mutex::RawMutex::new()),
                       DontShare::new(stack_mutex::RawMutex::new())],
        }
    }

    pub fn lock(&self) {
        // Spin a bit before falling back to the stack lock
        let mut counter = 0;
        loop {
            if self.spin_mutex.try_lock() {
                return;
            }
            if counter > LOOPS {
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

        let lock = shuffle(unsafe { libc::sched_getcpu() } as usize) as usize % NUM_FALLBACK;
        {
            self.fallback[lock].lock();

            self.spin_mutex.lock();

            self.fallback[lock].unlock();
        }
    }

    pub fn unlock(&self) {
        self.spin_mutex.unlock();
    }
}

fn shuffle(x: usize) -> u8 {
    SHUFFLE[x % SHUFFLE.len()]
}

// 32 cores is enough for anybody ;)
// Pseudo-randomly shuffle core ids to avoid CPU topology issues
const SHUFFLE: [u8; 32] = [25, 16, 24, 13, 20, 0, 18, 21, 9, 23, 5, 19, 15, 11, 28, 14, 10, 29,
                           30, 7, 1, 6, 27, 26, 3, 8, 2, 12, 4, 17, 22, 31];
