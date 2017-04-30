#![feature(integer_atomics)]

extern crate criterion;

#[macro_use]
extern crate syscall;

extern crate qlock_util;

use criterion::Criterion;

mod contend;

use qlock_util::cacheline::CacheLineAligned;
use qlock_util::backoff;

use std::mem;
use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use contend::{TestCase, contend};

const NUM_LOOPS: usize = 40;

struct Futex {
    val: CacheLineAligned<AtomicU32>,
}

struct FutexGuard<'r> {
    lock: &'r Futex,
}
const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl Futex {
    #[inline(never)]
    fn new() -> Futex {
        Futex { val: CacheLineAligned::new(AtomicU32::new(0)) }
    }

    #[inline(never)]
    fn lock<'r>(&'r self) -> FutexGuard<'r> {
        let mut result;
        match self.val.compare_exchange(0, 1, Ordering::AcqRel, Ordering::Relaxed) {
            Err(x) => result = x,
            Ok(_) => return FutexGuard { lock: self },
        }

        if result != 2 {
            result = self.val.swap(2, Ordering::Release);
        }
        if result == 0 {
            atomic::fence(Ordering::Acquire);
            return FutexGuard { lock: self };
        }

        backoff::pause();
        thread::yield_now();

        loop {
            let mut counter = 0;
            loop {
                if self.val.load(Ordering::Relaxed) != 2 {
                    result = self.val.swap(2, Ordering::Release);
                    if 0 == result {
                        atomic::fence(Ordering::Acquire);
                        return FutexGuard { lock: self };
                    }
                }
                if counter > NUM_LOOPS {
                    break;
                }

                backoff::pause();
                thread::yield_now();
                counter += 1;
            }

            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAIT_PRIVATE, 2, 0);
            }
        }
    }
}
impl<'r> Drop for FutexGuard<'r> {
    #[inline(never)]
    fn drop(&mut self) {
        if self.lock.val.fetch_sub(1, Ordering::Release) != 1 {
            self.lock.val.store(0, Ordering::Release);
            unsafe {
                let val_ptr: usize = mem::transmute(&self.lock.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAKE_PRIVATE, 1);
            }
        }
    }
}

enum FutexTestCase {}

impl TestCase for FutexTestCase {
    type TestType = Arc<Futex>;

    fn create_value() -> Self::TestType {
        Arc::new(Futex::new())
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
