extern crate criterion;
extern crate parking_lot;

mod contend;

use parking_lot::Mutex;
use std::marker::PhantomData;
use std::sync::Arc;
use criterion::Criterion;
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
            // do nothing
        }
    }
}

fn main() {
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_park",
                                                    |b, &&n| contend(phantom, |f| b.iter(f), n),
                                                    contend::STANDARD_TESTS.iter());
}
