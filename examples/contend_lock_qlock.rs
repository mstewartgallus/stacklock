extern crate criterion;
extern crate qlock;

mod contend;

use qlock::{QLock, QLockNode};

use criterion::Criterion;
use std::sync::Arc;

use contend::{TestCase, contend};

enum QLockTestCase {}

impl TestCase for QLockTestCase {
    type TestType = Arc<QLock>;

    fn create_value() -> Self::TestType {
        Arc::new(QLock::new())
    }
    fn do_stuff_with_value(value: &Self::TestType, times: usize) {
        let borrowed = &*value;
        for _ in 0..times {
            let mut node = QLockNode::new();
            let _ = borrowed.lock(&mut node);
        }
    }
}

fn main() {
    Criterion::default().bench_function("contend_lock_qlock", |b| {
        contend::<QLockTestCase>(b);
    });
}
