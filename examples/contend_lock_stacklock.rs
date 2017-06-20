extern crate criterion;
extern crate stacklock;

mod contend;

use stacklock::Mutex;

use criterion::Criterion;
use std::sync::Arc;

use contend::{TestCase, contend};

enum MyTestCase {}

impl TestCase for MyTestCase {
    type TestType = Arc<Mutex<()>>;

    fn create_value() -> Self::TestType {
        Arc::new(Mutex::new(()))
    }
    fn do_stuff_with_value(value: &Self::TestType, times: usize) {
        let borrowed = &*value;
        for _ in 0..times {
            let _ = borrowed.lock();
        }
    }
}

fn main() {
    Criterion::default().bench_function_over_inputs("contend_lock_stacklock",
                                                    |b, &&n| contend::<MyTestCase>(b, n),
                                                    contend::STANDARD_TESTS.iter());
}
