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
    fn do_stuff_with_value(value: &Self::TestType, times: usize) {
        let borrowed = &*value;
        for _ in 0..times {
            let _ = borrowed.lock();
            // do nothing
        }
    }
}

fn main() {
    Criterion::default().bench_function_over_inputs("contend_lock_park",
                                                    |b, &&n| contend::<MutexTestCase>(b, n),
                                                    contend::STANDARD_TESTS.iter());
}
