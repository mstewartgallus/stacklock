#![feature(test)]
#![feature(integer_atomics)]
extern crate test;

mod contend;

extern crate qlock_util;

use qlock_util::cacheline::CacheLineAligned;
use qlock_util::backoff;
use qlock_util::exp;

use std::thread;
use std::time::Duration;
use std::sync::atomic::{AtomicU32, Ordering};

use contend::{TestCase, contend};

const SLEEP_NS: usize = 400;
const NUM_LOOPS: usize = 30;
const MAX_LOG_NUM_PAUSES: usize = 7;

struct Ticket {
    high: CacheLineAligned<AtomicU32>,
    low: CacheLineAligned<AtomicU32>,
}

struct TicketGuard<'r> {
    lock: &'r Ticket,
}

impl Ticket {
    fn new() -> Ticket {
        Ticket {
            high: CacheLineAligned::new(AtomicU32::new(0)),
            low: CacheLineAligned::new(AtomicU32::new(0)),
        }
    }

    fn lock<'r>(&'r self) -> TicketGuard<'r> {
        let my_ticket = self.high.fetch_add(1, Ordering::AcqRel);
        let mut counter = 0;
        let mut current_ticket;
        loop {
            current_ticket = self.low.load(Ordering::Acquire);
            if current_ticket == my_ticket {
                return TicketGuard { lock: self };
            }
            if counter < NUM_LOOPS {
                for _ in 0..backoff::thread_num(exp::exp(counter, NUM_LOOPS, MAX_LOG_NUM_PAUSES)) {
                    backoff::pause();
                }
                counter += 1;
            } else {
                thread::sleep(Duration::new(0, backoff::thread_num(SLEEP_NS) as u32));
            }
        }
    }
}
impl<'r> Drop for TicketGuard<'r> {
    fn drop(&mut self) {
        self.lock.low.fetch_add(1, Ordering::AcqRel);
    }
}

enum TicketTestCase {}

impl TestCase for TicketTestCase {
    type TestType = Ticket;

    fn create_value() -> Ticket {
        Ticket::new()
    }
    fn do_stuff_with_value(value: &Ticket) {
        let _ = value.lock();
        // do nothing
    }
}

#[bench]
fn contend_lock_ticket(b: &mut test::Bencher) {
    contend::<TicketTestCase>(b);
}
