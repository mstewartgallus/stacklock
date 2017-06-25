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
use std::thread;

use dontshare::DontShare;
use sleepfast;
use weakrand;

use stack_mutex::StackMutex;
use try_mutex::TryMutex;

const MAX_EXP: usize = 8;

// A simple test-and test and set lock causes lots of intercore
// commmunication when contended by lots of threads.  A StackMutex has
// a bunch of overhead.  Use a test-and-test and set lock that falls
// back to a StackMutex under heavy contention.
pub struct RawMutex {
    try_mutex: DontShare<TryMutex>,
    fallback: DontShare<StackMutex>,
}
unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

pub struct RawMutexGuard<'r> {
    lock: &'r RawMutex,
}

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex {
            try_mutex: DontShare::new(TryMutex::new()),
            fallback: DontShare::new(StackMutex::new()),
        }
    }

    pub fn lock<'r>(&'r self) -> RawMutexGuard<'r> {
        if self.try_mutex.try_acquire() {
            return RawMutexGuard { lock: self };
        }

        let _fallback_guard = self.fallback.lock();
        let mut counter = 0;
        loop {
            if self.try_mutex.try_acquire() {
                return RawMutexGuard { lock: self };
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
    }
}
impl<'r> Drop for RawMutexGuard<'r> {
    fn drop(&mut self) {
        self.lock.try_mutex.release();
    }
}
