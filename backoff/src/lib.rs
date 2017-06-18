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
#![feature(hint_core_should_pause)]
#![feature(attr_literals)]

use std::sync::atomic;

#[inline(always)]
pub fn pause_times(spins: u64) {
    if 0 == spins {
        return;
    }
    let unroll = 8;
    let start_loops = spins % unroll;
    let outer_loops = spins / unroll;

    // Implement duff's device in Rust
    'do_0: loop {
        'do_1: loop {
            'do_2: loop {
                'do_3: loop {
                    'do_4: loop {
                        'do_5: loop {
                            'do_6: loop {
                                match start_loops {
                                    0 => break 'do_0,
                                    1 => break 'do_1,
                                    2 => break 'do_2,
                                    3 => break 'do_3,
                                    4 => break 'do_4,
                                    5 => break 'do_5,
                                    6 => break 'do_6,
                                    7 => {}
                                    _ => unreachable!(),
                                }
                                atomic::hint_core_should_pause();
                                break;
                            }
                            atomic::hint_core_should_pause();
                            break;
                        }
                        atomic::hint_core_should_pause();
                        break;
                    }
                    atomic::hint_core_should_pause();
                    break;
                }
                atomic::hint_core_should_pause();
                break;
            }
            atomic::hint_core_should_pause();
            break;
        }
        atomic::hint_core_should_pause();
        break;
    }

    let mut counter = outer_loops;
    loop {
        match counter.checked_sub(1) {
            None => break,
            Some(newcounter) => {
                counter = newcounter;
            }
        }

        for _ in 0..unroll {
            atomic::hint_core_should_pause();
        }
    }
}