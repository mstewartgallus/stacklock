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
#![feature(asm)]
#![feature(const_fn)]
#![feature(integer_atomics)]
#![feature(hint_core_should_pause)]

#[cfg(feature = "lin-log")]
#[macro_use]
extern crate lazy_static;

#[macro_use]
extern crate syscall;

extern crate libc;

extern crate sleepfast;

extern crate dontshare;
extern crate weakrand;

mod notifier;
mod raw_mutex;
mod try_mutex;
mod stack_mutex;

use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use raw_mutex::{RawMutex, RawMutexGuard};

pub struct Mutex<T: ?Sized> {
    mutex: RawMutex,
    data: UnsafeCell<T>,
}
unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}

pub struct MutexGuard<'r, T: ?Sized + 'r> {
    _guard: RawMutexGuard<'r>,
    lock: &'r Mutex<T>,
    _phantom: PhantomData<&'r mut T>,
}

impl<T> Mutex<T> {
    pub fn new(val: T) -> Self {
        Mutex {
            mutex: RawMutex::new(),
            data: UnsafeCell::new(val),
        }
    }

    pub fn into_inner(self) -> T {
        unsafe { self.data.into_inner() }
    }
}

impl<T: ?Sized> Mutex<T> {
    pub fn lock<'r>(&'r self) -> MutexGuard<'r, T> {
        return MutexGuard {
            _guard: self.mutex.lock(),
            lock: self,
            _phantom: PhantomData,
        };
    }
}

impl<T: ?Sized + Default> Default for Mutex<T> {
    fn default() -> Mutex<T> {
        Mutex::new(Default::default())
    }
}

impl<'a, T: ?Sized + 'a> Deref for MutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T: ?Sized + 'a> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}
