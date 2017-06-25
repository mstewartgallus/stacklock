#![feature(integer_atomics)]

#[macro_use]
extern crate syscall;
extern crate sleepfast;
extern crate criterion;
extern crate dontshare;
extern crate weakrand;

mod contend;

use criterion::Criterion;

use dontshare::DontShare;

use std::mem;
use std::marker::PhantomData;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::thread;

use contend::{TestCase, contend};

const NUM_LOOPS: usize = 30;
const MAX_EXP: usize = 9;
const YIELD_INTERVAL: usize = 8;

const FUTEX_WAIT_BITSET_PRIVATE: usize = 9 | 128;
const FUTEX_WAKE_BITSET_PRIVATE: usize = 10 | 128;

struct Ticket {
    high: DontShare<AtomicU32>,
    low: DontShare<AtomicU32>,
    spinners: DontShare<AtomicU32>,
}

struct TicketGuard<'r> {
    lock: &'r Ticket,
    ticket: u32,
}

impl Ticket {
    #[inline(never)]
    fn new() -> Ticket {
        Ticket {
            high: DontShare::new(AtomicU32::new(0)),
            low: DontShare::new(AtomicU32::new(0)),
            spinners: DontShare::new(AtomicU32::new(0)),
        }
    }

    #[inline(never)]
    fn lock<'r>(&'r self) -> TicketGuard<'r> {
        let my_ticket = self.high.fetch_add(1, Ordering::AcqRel);
        let mut current_ticket;
        loop {
            let mut counter = 0;
            loop {
                current_ticket = self.low.load(Ordering::Relaxed);
                if current_ticket == my_ticket {
                    return TicketGuard {
                        lock: self,
                        ticket: my_ticket,
                    };
                }
                if counter >= NUM_LOOPS {
                    break;
                }
                if counter % YIELD_INTERVAL == YIELD_INTERVAL - 1 {
                    thread::yield_now();
                }
                let exp;
                if counter > MAX_EXP {
                    exp = 1 << MAX_EXP;
                } else {
                    exp = 1 << counter;
                }
                sleepfast::pause_times(weakrand::rand(1, exp) as usize);
                counter = counter.wrapping_add(1);
            }

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
        }
    }
}
impl<'r> Drop for TicketGuard<'r> {
    #[inline(never)]
    fn drop(&mut self) {
        self.lock.low.fetch_add(1, Ordering::Release);
        let num = (self.ticket.wrapping_add(1)) % 32;

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

enum MyTestCase {}

impl TestCase for MyTestCase {
    type TestType = Arc<Ticket>;

    fn create_value() -> Self::TestType {
        Arc::new(Ticket::new())
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
    Criterion::default().bench_function_over_inputs("contend_lock_ticket",
                                                    |b, &&n| contend(phantom, |f| { b.iter(|| f()) }, n),
                                                    contend::STANDARD_TESTS.iter());
}
