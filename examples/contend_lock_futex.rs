#![feature(integer_atomics)]

extern crate criterion;

#[macro_use]
extern crate syscall;

extern crate sleepfast;
extern crate dontshare;
extern crate weakrand;

use criterion::Criterion;

mod contend;

use contend::{TestCase, contend};
use dontshare::DontShare;
use std::mem;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

const NUM_LOOPS: usize = 200;
const MAX_EXP: usize = 8;

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const LOCKED_WITH_WAITER: u32 = 2;

/// This is basically Ulrich-Drepper's futexes are tricky futex lock
pub struct RawMutex {
    val: DontShare<AtomicU32>,
}
pub struct RawMutexGuard<'r> {
    lock: &'r RawMutex,
}
const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl RawMutex {
    #[inline(always)]
    pub fn new() -> RawMutex {
        RawMutex { val: DontShare::new(AtomicU32::new(UNLOCKED)) }
    }

    pub fn try_lock<'r>(&'r self) -> Option<RawMutexGuard<'r>> {
        if self.val
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok() {
            return Some(RawMutexGuard { lock: self });
        }
        return None;
    }

    pub fn lock<'r>(&'r self) -> RawMutexGuard<'r> {
        if let Err(newval) = self.val
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::SeqCst, Ordering::Relaxed) {
            if newval == LOCKED {
                if UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
                    return RawMutexGuard { lock: self };
                }
            }
        } else {
            return RawMutexGuard { lock: self };
        }

        'big_loop: loop {
            let mut counter = 0;
            loop {
                if UNLOCKED == self.val.load(Ordering::Relaxed) {
                    if UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
                        break 'big_loop;
                    }
                }

                if counter > NUM_LOOPS {
                    break;
                }

                thread::yield_now();

                let exp = if counter < MAX_EXP {
                    1 << counter
                } else {
                    1 << MAX_EXP
                };

                counter = counter.wrapping_add(1);

                let spins = weakrand::rand(1, exp);

                sleepfast::pause_times(spins as usize);
            }
            // reset spin bit
            if self.val.load(Ordering::Relaxed) != LOCKED {
                if self.val.swap(LOCKED, Ordering::SeqCst) == UNLOCKED {
                    break 'big_loop;
                }
            }
            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAIT_PRIVATE, LOCKED_WITH_WAITER, 0);
            }
        }

        return RawMutexGuard { lock: self };
    }
}
impl<'r> Drop for RawMutexGuard<'r> {
    fn drop(&mut self) {
        if self.lock.val.swap(UNLOCKED, Ordering::SeqCst) == LOCKED_WITH_WAITER {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.lock.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAKE_PRIVATE, 1);
            }
        }
    }
}

enum FutexTestCase {}

impl TestCase for FutexTestCase {
    type TestType = Arc<RawMutex>;

    fn create_value() -> Self::TestType {
        Arc::new(RawMutex::new())
    }
    fn do_stuff_with_value(value: &Self::TestType, times: usize) {
        let borrowed = &*value;
        for _ in 0..times {
            let _ = borrowed.lock();
            // do nothing
        }
    }
}

fn main() {
    Criterion::default().bench_function_over_inputs("contend_lock_futex",
                                                    |b, &&n| contend::<FutexTestCase>(b, n),
                                                    contend::STANDARD_TESTS.iter());
}
