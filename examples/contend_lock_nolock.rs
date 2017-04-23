extern crate criterion;

mod contend;

use contend::{TestCase, contend};
use criterion::Criterion;

enum EmptyTestCase {}
impl TestCase for EmptyTestCase {
    type TestType = ();

    fn create_value() -> () {
        return ();
    }

    fn do_stuff_with_value(_: &()) {
        // do nothing
    }
}

fn main() {
    Criterion::default().bench_function("contend_lock_nolock", |b| {
        contend::<EmptyTestCase>(b);
    });
}
