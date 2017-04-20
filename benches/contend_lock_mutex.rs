#![feature(test)]
extern crate test;

mod contend;

use std::sync::{Arc, Mutex};
use contend::{TestCase, contend};

enum MutexTestCase {}

impl TestCase for MutexTestCase {
    type TestType = Arc<Mutex<()>>;

    fn create_value() -> Self::TestType {
        Arc::new(Mutex::new(()))
    }
    fn do_stuff_with_value(value: &Self::TestType) {
        let _ = value.lock().unwrap();
        // do nothing
    }
}

#[bench]
fn contend_lock_mutex(b: &mut test::Bencher) {
    contend::<MutexTestCase>(b);
}
