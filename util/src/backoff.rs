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
use std::cell::RefCell;
use std::usize;

use rand::{Rng, XorShiftRng};
use rand;

#[inline]
pub fn pause() {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe {
        asm!("pause" ::: "memory" : "volatile");
    }

    #[cfg(target_arch = "aarch64")]
    unsafe {
        asm!("yield" ::: "memory" : "volatile");
    }
}

// Just use Knuth's MMIX LCG.

thread_local! {
    static RNG: RefCell<XorShiftRng> = RefCell::new(rand::weak_rng());
}

/// A thread random number
#[inline]
pub fn thread_num(max: usize) -> usize {
    return RNG.with(|rng| rng.borrow_mut().gen_range(0, max + 1));
}