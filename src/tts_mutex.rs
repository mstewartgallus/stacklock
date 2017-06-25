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
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;

use sleepfast;
use weakrand;

const MAX_EXP: usize = 8;

/// A simple test and test and set mutex
pub struct RawMutex {
    locked: AtomicBool,
}
pub struct RawMutexGuard<'r> {
    lock: &'r RawMutex,
}

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { locked: AtomicBool::new(false) }
    }

    pub fn try_lock<'r>(&'r self) -> Option<RawMutexGuard<'r>> {
        let locked = self.locked.load(Ordering::Relaxed);
        if locked {
            return None;
        }

        if !self.locked.swap(true, Ordering::SeqCst) {
            return Some(RawMutexGuard { lock: self });
        }

        return None;
    }

    pub fn lock<'r>(&'r self) -> RawMutexGuard<'r> {
        let mut counter = 0;
        loop {
            if let Some(guard) = self.try_lock() {
                return guard;
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
        self.lock.locked.store(false, Ordering::SeqCst);
    }
}
