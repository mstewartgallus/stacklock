#![feature(asm)]
#![feature(integer_atomics)]
extern crate criterion;
extern crate qlock_util;

mod contend;

use qlock_util::backoff;
use qlock_util::cacheline::CacheLineAligned;

use criterion::Criterion;
use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};

use contend::{TestCase, contend};

const MAX_EXP: usize = 9;

struct Hle {
    val: CacheLineAligned<AtomicU32>,
}

struct HleGuard<'r> {
    lock: &'r Hle,
}

impl Hle {
    #[inline(never)]
    fn new() -> Hle {
        Hle { val: CacheLineAligned::new(AtomicU32::new(0)) }
    }

    #[inline(never)]
    fn lock<'r>(&'r self) -> HleGuard<'r> {
        if self.val.load(Ordering::Relaxed) == 0 {
            let mut prev: u32 = 1;
            unsafe {
                // xchg implicitly has a lock prefix
                asm!("xacquire; xchg $0, $1"
                     : "+r" (prev), "+*m" (&*self.val)
                     :
                     : "memory"
                     : "volatile", "intel");
            }
            if 0 == prev {
                atomic::fence(Ordering::Acquire);
                return HleGuard { lock: self };
            }
        }

        let mut counter = 0;
        loop {
            backoff::yield_now();
            let exp;
            if counter > MAX_EXP {
                exp = 1 << MAX_EXP;
            } else {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            }

            backoff::pause_times(backoff::thread_num(1, exp));

            if self.val.load(Ordering::Relaxed) == 0 {
                let mut prev: u32 = 1;
                unsafe {
                    // xchg implicitly has a lock prefix
                    asm!("xacquire; xchg $0, $1"
                         : "+r" (prev), "+*m" (&*self.val)
                         :
                         : "memory"
                         : "volatile", "intel");
                }
                if 0 == prev {
                    atomic::fence(Ordering::Acquire);
                    return HleGuard { lock: self };
                }
            }
        }
    }
}
impl<'r> Drop for HleGuard<'r> {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            asm!("xrelease; mov dword ptr $0, 0"
                 : "=*m" (&self.lock.val)
                 :
                 : "memory"
                 : "volatile", "intel");
        }
    }
}

enum HleTestCase {}

impl TestCase for HleTestCase {
    type TestType = Arc<Hle>;

    fn create_value() -> Self::TestType {
        Arc::new(Hle::new())
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
    Criterion::default().bench_function_over_inputs("contend_lock_hle",
                                                    |b, &&n| contend::<HleTestCase>(b, n),
                                                    contend::STANDARD_TESTS.iter());
}
