#![feature(asm)]
#![feature(integer_atomics)]
extern crate criterion;
extern crate sleepfast;
extern crate dontshare;
extern crate weakrand;

mod contend;

use dontshare::DontShare;

use criterion::Criterion;
use std::marker::PhantomData;
use std::sync::Arc;
use std::sync::atomic;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use contend::{TestCase, contend};

const MAX_EXP: usize = 9;

struct Hle {
    val: DontShare<AtomicU32>,
}

struct HleGuard<'r> {
    lock: &'r Hle,
}

impl Hle {
    #[inline(never)]
    fn new() -> Hle {
        Hle { val: DontShare::new(AtomicU32::new(0)) }
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
            thread::yield_now();
            let exp;
            if counter > MAX_EXP {
                exp = 1 << MAX_EXP;
            } else {
                exp = 1 << counter;
                counter = counter.wrapping_add(1);
            }

            sleepfast::pause_times(weakrand::rand(1, exp) as usize);

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

enum MyTestCase {}

impl TestCase for MyTestCase {
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
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_hle",
                                                    |b, &&n| contend(phantom, |f| { b.iter(|| f()) }, n),
                                                    contend::STANDARD_TESTS.iter());
}
