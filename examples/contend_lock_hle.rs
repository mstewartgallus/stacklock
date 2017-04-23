#![feature(asm)]
#![feature(integer_atomics)]
extern crate criterion;
extern crate qlock_util;

mod contend;

use qlock_util::cacheline::CacheLineAligned;

use criterion::Criterion;
use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};

use std::thread;

use contend::{TestCase, contend};

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
        loop {
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

            thread::yield_now();
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
    fn do_stuff_with_value(value: &Self::TestType) {
        let _ = value.lock();
        // do nothing
    }
}

fn main() {
    Criterion::default().bench_function("contend_lock_hle", |b| {
        contend::<HleTestCase>(b);
    });
}
