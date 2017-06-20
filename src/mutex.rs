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
use std::cmp;
use std::sync::atomic::{AtomicU8, Ordering};
use std::thread;

use dontshare::DontShare;
use sleepfast;
use weakrand;

#[derive(Clone, Copy, PartialEq, Eq)]
struct LockState {
    state: u8,
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
    state: AtomicU8,
}
impl AtomicLockState {
    fn new(state: LockState) -> Self {
        AtomicLockState { state: AtomicU8::new(state.state) }
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
        match self.state.compare_exchange_weak(old.state, new.state, success, fail) {
            Ok(x) => Ok(LockState { state: x }),
            Err(x) => Err(LockState { state: x }),
        }
    }
}

pub struct RawMutex {
    state: DontShare<AtomicLockState>,
}

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum SpinState {
    Spinner,
    NoSpinner,
}

const MAX_EXP: usize = 8;
const LOOPS: usize = 10;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> Self {
        RawMutex { state: DontShare::new(AtomicLockState::new(LockState::new(false, false))) }
    }

    pub fn try_acquire(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        if state.locked() {
            return false;
        }

        let mut counter = 0;
        loop {
            let dblcheck = self.state.load(Ordering::Relaxed);
            if dblcheck != state {
                state = dblcheck;
            } else {
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
            }
            thread::yield_now();

            let spins = weakrand::rand(1, 1 << counter);

            sleepfast::pause_times(spins as usize);

            if counter < MAX_EXP {
                counter = counter.wrapping_add(1);
            }
        }
    }

    pub fn spin_try_acquire(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);

        let mut counter = 0usize;
        loop {
            if state.locked() {
                if !state.has_spinner() {
                    let dblcheck = self.state.load(Ordering::Relaxed);
                    if dblcheck != state {
                        state = dblcheck;
                    } else {
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
                }
            } else {
                let dblcheck = self.state.load(Ordering::Relaxed);
                if dblcheck != state {
                    state = dblcheck;
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
            }

            if counter > LOOPS {
                break;
            }
            thread::yield_now();

            let spins = weakrand::rand(1, 1 << cmp::min(counter, MAX_EXP));

            sleepfast::pause_times(spins as usize);

            counter = counter.wrapping_add(1);
        }

        // temporarily set no spinners (others will refresh the bit on
        // later spins)
        counter = 0;
        loop {
            let dblcheck = self.state.load(Ordering::Relaxed);
            if dblcheck != state {
                state = dblcheck;
            } else {
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
            }
            thread::yield_now();

            let spins = weakrand::rand(1, 1 << counter);

            sleepfast::pause_times(spins as usize);

            if counter < MAX_EXP {
                counter = counter.wrapping_add(1);
            }
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
