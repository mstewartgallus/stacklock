#![feature(test)]
#![feature(asm)]
#![feature(integer_atomics)]
extern crate test;

mod contend;

extern crate qlock_util;

use qlock_util::cacheline::CacheLineAligned;
use qlock_util::backoff;
use qlock_util::exp;

use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};

use std::time::Duration;
use std::thread;

use contend::{TestCase, contend};

const NUM_LOOPS: usize = 50;
const MAX_LOG_NUM_PAUSES: usize = 7;

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
            let mut counter = 0;
            loop {
                let mut prev: u32 = 1;
                unsafe {
                    asm!("xacquire; lock; xchg $0, $1"
                         : "+r" (prev), "+*m" (&*self.val)
                         :
                         : "memory"
                         : "volatile", "intel");
                }
                if 0 == prev {
                    atomic::fence(Ordering::Acquire);
                    return HleGuard { lock: self };
                }

                if counter > NUM_LOOPS {
                    break;
                }

                for _ in 0..backoff::thread_num(exp::exp(counter, NUM_LOOPS, MAX_LOG_NUM_PAUSES)) {
                    backoff::pause();
                }
                counter += 1;
            }

            thread::sleep(Duration::new(0, backoff::thread_num(400) as u32));
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

#[bench]
fn contend_lock_hle(b: &mut test::Bencher) {
    contend::<HleTestCase>(b);
}
