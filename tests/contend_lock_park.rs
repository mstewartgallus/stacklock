extern crate criterion;
extern crate parking_lot;

mod contend;

use parking_lot::Mutex;
use std::sync::Arc;
use criterion::Criterion;
use contend::{TestCase, contend};

enum MutexTestCase {}

impl TestCase for MutexTestCase {
    type TestType = Arc<Mutex<()>>;

    fn create_value() -> Self::TestType {
        Arc::new(Mutex::new(()))
    }
    fn do_stuff_with_value(value: &Self::TestType) {
        let _ = value.lock();
        // do nothing
    }
}

#[test]
fn contend_lock_park() {
    Criterion::default().bench_function("contend_lock_park", |b| {
        contend::<MutexTestCase>(b);
    });
}
