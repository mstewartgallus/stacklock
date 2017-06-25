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
use dontshare::DontShare;
use weakrand;
use sleepfast;

use stack_mutex;
use tts_mutex;

use std::thread;


const MAX_EXP: usize = 8;
const LOOPS: usize = 10;

// A simple test-and test and set lock causes lots of intercore
// commmunication when contended by lots of threads.  A StackMutex has
// a bunch of overhead.  Use a test-and-test and set lock that falls
// back to a StackMutex under heavy contention.
pub struct RawMutex {
    spin_mutex: DontShare<tts_mutex::RawMutex>,
    fallback: DontShare<stack_mutex::RawMutex>,
}
unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

pub struct RawMutexGuard<'r> {
    _guard: tts_mutex::RawMutexGuard<'r>,
}

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex {
            spin_mutex: DontShare::new(tts_mutex::RawMutex::new()),
            fallback: DontShare::new(stack_mutex::RawMutex::new()),
        }
    }

    pub fn lock<'r>(&'r self) -> RawMutexGuard<'r> {
        // Spin a bit before falling back to the stack lock
        let mut counter = 0;
        loop {
            if let Some(guard) = self.spin_mutex.try_lock() {
                return RawMutexGuard { _guard: guard };
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

        let guard;
        {
            let _fallback_guard = self.fallback.lock();

            guard = self.spin_mutex.lock();
        }
        return RawMutexGuard { _guard: guard };
    }
}
