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
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use dontshare::DontShare;
use sleepfast;
use weakrand;

const YIELD_INTERVAL: usize = 4;
const MAX_EXP: usize = 8;
const LOOPS: usize = 10;

#[derive(Clone, Copy, PartialEq, Eq)]
struct LockState {
    state: u32,
}
impl LockState {
    fn new(locked: bool, has_spinner: bool) -> Self {
        let mut state = LockState { state: 0 };
        if locked {
            state = state.set_locked();
        }
        if has_spinner {
            state = state.set_has_spinner();
        }
        return state;
    }
    fn locked(&self) -> bool {
        (self.state & 1) != 0
    }
    fn set_locked(&self) -> LockState {
        LockState { state: self.state | 1 }
    }

    fn has_spinner(&self) -> bool {
        (self.state & (1 << 1)) != 0
    }
    fn set_has_spinner(&self) -> LockState {
        LockState { state: self.state | (1 << 1) }
    }
    fn set_has_no_spinner(&self) -> LockState {
        LockState { state: self.state & !(1 << 1) }
    }
}

struct AtomicLockState {
    state: AtomicU32,
}
impl AtomicLockState {
    fn new(state: LockState) -> Self {
        AtomicLockState { state: AtomicU32::new(state.state) }
    }
    fn load(&self, ordering: Ordering) -> LockState {
        LockState { state: self.state.load(ordering) }
    }

    fn swap(&self, new: LockState, ordering: Ordering) -> LockState {
        LockState { state: self.state.swap(new.state, ordering) }
    }

    fn compare_exchange_weak(&self,
                             old: LockState,
                             new: LockState,
                             success: Ordering,
                             fail: Ordering)
                             -> Result<LockState, LockState> {
        // Test and test and set optimization
        let mut dblcheck = self.state.load(fail);
        if dblcheck == old.state {
            match self.state.compare_exchange_weak(old.state, new.state, success, fail) {
                Ok(x) => return Ok(LockState { state: x }),
                Err(x) => {
                    dblcheck = x;
                }
            }
        }
        return Err(LockState { state: dblcheck });
    }
}

pub struct TryMutex {
    state: DontShare<AtomicLockState>,
}

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum SpinState {
    Spinner,
    NoSpinner,
}

impl TryMutex {
    #[inline(always)]
    pub fn new() -> Self {
        TryMutex { state: DontShare::new(AtomicLockState::new(LockState::new(false, false))) }
    }

    pub fn try_acquire(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        if state.locked() {
            return false;
        }

        let mut counter = 0;
        loop {
            match self.state.compare_exchange_weak(state,
                                                   state.set_locked(),
                                                   Ordering::SeqCst,
                                                   Ordering::Relaxed) {
                Ok(_) => return true,
                Err(newstate) => {
                    state = newstate;
                    if state.locked() {
                        return false;
                    }
                }
            }
            thread::yield_now();

            let exp;
            if counter < MAX_EXP {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            } else {
                exp = 1 << MAX_EXP;
            }

            let spins = weakrand::rand(1, exp);

            sleepfast::pause_times(spins as usize);
        }
    }

    pub fn spin_try_acquire(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);

        let mut counter = 0usize;
        loop {
            if state.locked() {
                if !state.has_spinner() {
                    match self.state.compare_exchange_weak(state,
                                                           state.set_has_spinner(),
                                                           Ordering::SeqCst,
                                                           Ordering::Relaxed) {
                        Ok(_) => {}
                        Err(newstate) => {
                            state = newstate;
                        }
                    }
                }
            } else {
                match self.state.compare_exchange_weak(state,
                                                       state.set_locked(),
                                                       Ordering::SeqCst,
                                                       Ordering::Relaxed) {
                    Ok(_) => return true,
                    Err(newstate) => {
                        state = newstate;
                    }
                }
            }

            if counter > LOOPS {
                break;
            }
            if counter % YIELD_INTERVAL == YIELD_INTERVAL - 1 {
                thread::yield_now();
            }

            let spins = weakrand::rand(1,
                                       if counter < MAX_EXP {
                                           1 << counter
                                       } else {
                                           1 << MAX_EXP
                                       });

            sleepfast::pause_times(spins as usize);

            counter = counter.wrapping_add(1);
        }

        // temporarily set no spinners (others will refresh the bit on
        // later spins)
        counter = 0;
        loop {
            if !state.has_spinner() {
                break;
            }
            if state.locked() {
                match self.state.compare_exchange_weak(state,
                                                       state.set_has_no_spinner(),
                                                       Ordering::SeqCst,
                                                       Ordering::Relaxed) {
                    Ok(_) => break,
                    Err(newstate) => {
                        state = newstate;
                    }
                }
            } else {
                // opportunistically try to grab a lock if it is unlocked
                match self.state.compare_exchange_weak(state,
                                                       state.set_locked(),
                                                       Ordering::SeqCst,
                                                       Ordering::Relaxed) {
                    Ok(_) => return true,
                    Err(newstate) => {
                        state = newstate;
                    }
                }
            }
            thread::yield_now();

            let exp;
            if counter < MAX_EXP {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            } else {
                exp = 1 << MAX_EXP;
            }

            let spins = weakrand::rand(1, exp);

            sleepfast::pause_times(spins as usize);
        }
        return false;
    }

    pub fn release(&self) -> SpinState {
        let state = self.state.swap(LockState::new(false, false), Ordering::SeqCst);
        return if state.has_spinner() {
            SpinState::Spinner
        } else {
            SpinState::NoSpinner
        };
    }
}
