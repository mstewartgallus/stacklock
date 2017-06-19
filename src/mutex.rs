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

use dontshare::DontShare;
use sleepfast;
use weakrand;

pub struct RawMutex {
    locked: DontShare<AtomicBool>,
}

const UNLOCKED: bool = false;
const LOCKED: bool = true;

const LOOPS: usize = 4;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { locked: DontShare::new(AtomicBool::new(UNLOCKED)) }
    }

    pub fn try_acquire(&self) -> bool {
        // Test and test and set optimization
        if LOCKED == self.locked.load(Ordering::Relaxed) {
            return false;
        }

        if self.locked
            .compare_exchange(UNLOCKED, LOCKED, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok() {
            return true;
        }
        return false;
    }

    pub fn spin_try_acquire(&self) -> bool {
        let mut counter = 0usize;
        loop {
            if self.try_acquire() {
                return true;
            }

            if counter > LOOPS {
                return false;
            }
            thread::yield_now();

            let spins = weakrand::rand(1, 1 << counter);

            sleepfast::pause_times(spins as usize);

            counter = counter.wrapping_add(1);
        }
    }

    pub fn release(&self) {
        self.locked.store(false, Ordering::SeqCst);
    }
}
