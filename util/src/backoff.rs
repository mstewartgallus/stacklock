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
use std::sync::atomic;

use rand::{Rng, XorShiftRng};
use rand;

#[inline(always)]
pub fn pause() {
    atomic::hint_core_should_pause();
}

#[inline(always)]
pub fn pause_times(spins: usize) {
    let unroll = 8;
    // Implement duff's device in Rust
    'do_0: loop {
        'do_1: loop {
            'do_2: loop {
                'do_3: loop {
                    'do_4: loop {
                        'do_5: loop {
                            'do_6: loop {
                                match spins % unroll {
                                    0 => break 'do_0,
                                    1 => break 'do_1,
                                    2 => break 'do_2,
                                    3 => break 'do_3,
                                    4 => break 'do_4,
                                    5 => break 'do_5,
                                    6 => break 'do_6,
                                    7 => {},
                                    _ => unreachable!()
                                }
                                pause();
                                break;
                            }
                            pause();
                            break;
                        }
                        pause();
                        break;
                    }
                    pause();
                    break;
                }
                pause();
                break;
            }
            pause();
            break;
        }
        pause();
        break;
    }

    for _ in 0..spins / unroll {
        for _ in 0..unroll {
            pause();
        }
    }
}

thread_local! {
    static RNG: RefCell<XorShiftRng> = RefCell::new(rand::weak_rng());
}

/// A thread random number
#[inline]
pub fn thread_num(min: usize, max: usize) -> usize {
    return RNG.with(|rng| rng.borrow_mut().gen_range(min, max + 1));
}
