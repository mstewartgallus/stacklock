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
use std::sync::atomic;
use std::sync::atomic::{AtomicBool, Ordering};

use qlock_util::cacheline::CacheLineAligned;

pub struct RawMutex {
    locked: CacheLineAligned<AtomicBool>,
}

const UNLOCKED: bool = false;
const LOCKED: bool = true;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { locked: CacheLineAligned::new(AtomicBool::new(UNLOCKED)) }
    }

    pub fn try_acquire(&self) -> bool {
        if LOCKED == self.locked.load(Ordering::Relaxed) {
            return false;
        }

        if self.locked
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok() {
            atomic::fence(Ordering::Acquire);
            return true;
        }
        return false;
    }

    pub fn release(&self) {
        self.locked.store(false, Ordering::Release);
    }
}
