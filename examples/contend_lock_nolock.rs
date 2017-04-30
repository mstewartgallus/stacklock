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

    fn do_stuff_with_value(_: &Self::TestType, _: usize) {
        // do nothing
    }
}

fn main() {
    Criterion::default().bench_function_over_inputs("contend_lock_nolock",
                                                    |b, &&n| contend::<EmptyTestCase>(b, n),
                                                    contend::STANDARD_TESTS.iter());
}
