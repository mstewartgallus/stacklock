#![feature(test)]
#![feature(integer_atomics)]
extern crate test;

mod contend;

#[macro_use]
extern crate syscall;

use std::mem;
use std::sync::atomic::{AtomicU32, Ordering};

use contend::{TestCase, contend};

struct Futex {
    val: AtomicU32,
}

struct FutexGuard<'r> {
    lock: &'r Futex,
}
const FUTEX_WAIT_PRIVATE: usize = 0 | 128;
const FUTEX_WAKE_PRIVATE: usize = 1 | 128;

impl Futex {
    fn new() -> Futex {
        Futex { val: AtomicU32::new(0) }
    }

    fn lock<'r>(&'r self) -> FutexGuard<'r> {
        let mut result;
        match self.val.compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire) {
            Err(x) => result = x,
            Ok(_) => return FutexGuard { lock: self },
        }

        if result != 2 {
            result = self.val.swap(2, Ordering::AcqRel);
        }
        if result == 0 {
            return FutexGuard { lock: self };
        }

        loop {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.val);
                syscall!(FUTEX, val_ptr, FUTEX_WAIT_PRIVATE, 2, 0);
            }
            for _ in 1..800 {
                if self.val.load(Ordering::Acquire) != 2 {
                    result = self.val.swap(2, Ordering::AcqRel);
                    if 0 == result {
                        return FutexGuard { lock: self };
                    }
                }
                // pause
            }
        }
    }
}
impl<'r> Drop for FutexGuard<'r> {
    fn drop(&mut self) {
        if self.lock.val.fetch_sub(1, Ordering::AcqRel) != 1 {
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
    type TestType = Futex;

    fn create_value() -> Futex {
        Futex::new()
    }
    fn do_stuff_with_value(value: &Futex) {
        let _ = value.lock();
        // do nothing
    }
}

#[bench]
fn contend_lock_futex(b: &mut test::Bencher) {
    contend::<FutexTestCase>(b);
}
