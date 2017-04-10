#![feature(test)]
extern crate test;

mod contend;

use std::sync::Mutex;
use contend::{TestCase, contend};

enum MutexTestCase {}

impl TestCase for MutexTestCase {
    type TestType = Mutex<()>;

    fn create_value() -> Mutex<()> {
        Mutex::new(())
    }
    fn do_stuff_with_value(value: &Mutex<()>) {
        let _ = value.lock().unwrap();
        // do nothing
    }
}

#[bench]
fn contend_lock_mutex(b: &mut test::Bencher) {
    contend::<MutexTestCase>(b);
}
