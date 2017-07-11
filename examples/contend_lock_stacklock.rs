extern crate criterion;
extern crate stacklock;

mod contend;

use stacklock::Mutex;

use criterion::Criterion;
use std::marker::PhantomData;
use std::env;
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
    let args: Vec<String> = env::args().collect();
    let num_threads: Vec<usize> =
        args.iter().skip(1).map(|s| s.parse::<usize>().unwrap()).collect();

    let test_borrow = &contend::STANDARD_TESTS;
    let inputs = if num_threads.is_empty() {
        test_borrow.iter()
    } else {
        num_threads.as_slice().iter()
    };
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_stacklock",
                                                    |b, &&n| contend(phantom, |f| b.iter(f), n),
                                                    inputs);
}
