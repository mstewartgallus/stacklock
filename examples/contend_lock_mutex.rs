extern crate criterion;

mod contend;

use criterion::Criterion;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};
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
            let _ = borrowed.lock().unwrap();
            // do nothing
        }
    }
}

fn main() {
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_mutex",
                                                    |b, &&n| contend(phantom, |f| b.iter(f), n),
                                                    contend::STANDARD_TESTS.iter());
}
