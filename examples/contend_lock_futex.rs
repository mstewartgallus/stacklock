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
use std::marker::PhantomData;
use std::mem;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

const INITIAL_LOOPS: usize = 20;
const NUM_LOOPS: usize = 20;
const MAX_EXP: usize = 8;

const UNLOCKED: u32 = 0;
const LOCKED: u32 = 1;
const LOCKED_WITH_WAITER: u32 = 2;

/// This is basically Ulrich-Drepper's futexes are tricky futex lock
struct RawMutex {
    val: DontShare<AtomicU32>,
}
struct RawMutexGuard<'r> {
    lock: &'r RawMutex,
}
const FUTEX_WAIT_PRIVATE: usize = 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl RawMutex {
    #[inline]
    fn new() -> RawMutex {
        RawMutex { val: DontShare::new(AtomicU32::new(UNLOCKED)) }
    }

    fn try_lock(&self) -> Option<RawMutexGuard> {
        if self.val.load(Ordering::Relaxed) != UNLOCKED {
            return None;
        }

        if self.val
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok() {
            Some(RawMutexGuard { lock: self })
        } else {
            None
        }
    }

    #[inline(never)]
    fn lock(&self) -> RawMutexGuard {
        {
            let mut counter = 0;
            loop {
                if let Some(guard) = self.try_lock() {
                    return guard;
                }

                if counter > INITIAL_LOOPS {
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
        }

        if UNLOCKED == self.val.load(Ordering::Relaxed) &&
           UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
            return RawMutexGuard { lock: self };
        }

        'big_loop: loop {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAIT_PRIVATE, LOCKED_WITH_WAITER, 0);
            }

            let mut counter = 0;
            loop {
                if UNLOCKED == self.val.load(Ordering::Relaxed) &&
                   UNLOCKED == self.val.swap(LOCKED_WITH_WAITER, Ordering::SeqCst) {
                    break 'big_loop;
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
        }

        RawMutexGuard { lock: self }
    }
}
impl<'r> Drop for RawMutexGuard<'r> {
    #[inline(never)]
    fn drop(&mut self) {
        if self.lock.val.swap(UNLOCKED, Ordering::SeqCst) == LOCKED_WITH_WAITER {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.lock.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAKE_PRIVATE, 1);
            }
        }
    }
}

enum MyTestCase {}

impl TestCase for MyTestCase {
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
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_futex",
                                                    |b, &&n| contend(phantom, |f| b.iter(f), n),
                                                    contend::STANDARD_TESTS.iter());
}
