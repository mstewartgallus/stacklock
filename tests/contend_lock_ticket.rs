#![feature(integer_atomics)]

#[macro_use]
extern crate syscall;
extern crate qlock_util;
extern crate criterion;

mod contend;

use criterion::Criterion;

use qlock_util::cacheline::CacheLineAligned;
use qlock_util::backoff;
use qlock_util::exp;

use std::mem;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use contend::{TestCase, contend};

const NUM_LOOPS: usize = 50;
const MAX_LOG_NUM_PAUSES: usize = 7;

const FUTEX_WAIT_BITSET_PRIVATE: usize = 9 | 128;
const FUTEX_WAKE_BITSET_PRIVATE: usize = 10 | 128;

struct Ticket {
    high: CacheLineAligned<AtomicU32>,
    low: CacheLineAligned<AtomicU32>,
    spinners: CacheLineAligned<AtomicU32>,
}

struct TicketGuard<'r> {
    lock: &'r Ticket,
    ticket: u32,
}

impl Ticket {
    #[inline(never)]
    fn new() -> Ticket {
        Ticket {
            high: CacheLineAligned::new(AtomicU32::new(0)),
            low: CacheLineAligned::new(AtomicU32::new(0)),
            spinners: CacheLineAligned::new(AtomicU32::new(0)),
        }
    }

    #[inline(never)]
    fn lock<'r>(&'r self) -> TicketGuard<'r> {
        let my_ticket = self.high.fetch_add(1, Ordering::AcqRel);
        let mut counter = 0;
        let mut current_ticket;
        loop {
            current_ticket = self.low.load(Ordering::Relaxed);
            if current_ticket == my_ticket {
                return TicketGuard {
                    lock: self,
                    ticket: my_ticket,
                };
            }
            if counter < NUM_LOOPS {
                for _ in 0..backoff::thread_num(exp::exp(counter, NUM_LOOPS, MAX_LOG_NUM_PAUSES)) {
                    backoff::pause();
                }
                counter += 1;
            } else {
                let num = my_ticket % 32;
                let bitset = 1u32 << num;
                self.spinners.fetch_or(bitset, Ordering::Release);
                unsafe {
                    let val_ptr: usize = mem::transmute(&self.low);
                    syscall!(FUTEX,
                             val_ptr,
                             FUTEX_WAIT_BITSET_PRIVATE,
                             current_ticket,
                             0,
                             0,
                             bitset);
                }
                counter = 0;
            }
        }
    }
}
impl<'r> Drop for TicketGuard<'r> {
    #[inline(never)]
    fn drop(&mut self) {
        self.lock.low.fetch_add(1, Ordering::Release);
        let num = (self.ticket + 1) % 32;

        let bitset = 1u32 << num;

        let old = self.lock.spinners.load(Ordering::Acquire);
        self.lock.spinners.fetch_and(!bitset, Ordering::Release);
        if (old & bitset) != 0 {
            unsafe {
                let val_ptr: usize = mem::transmute(&self.lock.low);
                syscall!(FUTEX,
                         val_ptr,
                         FUTEX_WAKE_BITSET_PRIVATE,
                         usize::max_value(),
                         0,
                         0,
                         bitset);
            }
        }
    }
}

enum TicketTestCase {}

impl TestCase for TicketTestCase {
    type TestType = Arc<Ticket>;

    fn create_value() -> Self::TestType {
        Arc::new(Ticket::new())
    }
    fn do_stuff_with_value(value: &Self::TestType) {
        let _ = value.lock();
        // do nothing
    }
}

#[test]
fn contend_lock_ticket() {
    Criterion::default().bench_function("contend_lock_ticket", |b| {
        contend::<TicketTestCase>(b);
    });
}
