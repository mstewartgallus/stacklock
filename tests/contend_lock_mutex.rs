extern crate criterion;

mod contend;

use criterion::Criterion;
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

#[test]
fn contend_lock_mutex() {
    Criterion::default().bench_function("contend_lock_mutex", |b| {
        contend::<MutexTestCase>(b);
    });
}
