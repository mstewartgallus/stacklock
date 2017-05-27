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
use std::sync::atomic::{AtomicU8, Ordering};

use qlock_util::cacheline::CacheLineAligned;

pub struct RawMutex {
    locked: CacheLineAligned<AtomicU8>,
}

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { locked: CacheLineAligned::new(AtomicU8::new(0)) }
    }

    pub fn try_acquire(&self) -> bool {
        if UNLOCKED == self.locked.load(Ordering::Relaxed) {
            let mut prev: u8 = LOCKED;
            unsafe {
                // xchg implicitly has a lock prefix
                asm!("xacquire; xchg $0, $1"
                     : "+r" (prev), "+*m" (&*self.locked)
                     :
                     : "memory"
                     : "volatile", "intel");
            }
            if UNLOCKED == prev {
                atomic::fence(Ordering::Acquire);
                return true;
            }
        }
        return false;
    }

    pub fn release(&self) {
        unsafe {
            asm!("xrelease; mov byte ptr $0, 0"
                 : "=*m" (&*self.locked)
                 :
                 : "memory"
                 : "volatile", "intel");
        }
    }
}
