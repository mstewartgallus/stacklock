extern crate criterion;

mod contend;

use contend::{TestCase, contend};
use criterion::Criterion;

use std::marker::PhantomData;

enum MyTestCase {}
impl TestCase for MyTestCase {
    type TestType = ();

    fn create_value() -> () {
        return ();
    }

    fn do_stuff_with_value(_: &Self::TestType, _: usize) {
        // do nothing
    }
}

fn main() {
    let phantom: PhantomData<MyTestCase> = PhantomData;
    Criterion::default().bench_function_over_inputs("contend_lock_nolock",
                                                    |b, &&n| contend(phantom, |f| { b.iter(|| f()) }, n),
                                                    contend::STANDARD_TESTS.iter());
}
