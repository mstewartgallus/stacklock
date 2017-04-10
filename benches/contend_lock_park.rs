#![feature(test)]
extern crate test;
extern crate parking_lot;

mod contend;

use parking_lot::Mutex;

use contend::{TestCase, contend};

enum MutexTestCase {}

impl TestCase for MutexTestCase {
    type TestType = Mutex<()>;

    fn create_value() -> Mutex<()> {
        Mutex::new(())
    }
    fn do_stuff_with_value(value: &Mutex<()>) {
        let _ = value.lock();
        // do nothing
    }
}

#[bench]
fn contend_lock_park(b: &mut test::Bencher) {
    contend::<MutexTestCase>(b);
}
