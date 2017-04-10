#![feature(test)]
extern crate test;

mod contend;

use contend::{TestCase, contend};

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

#[bench]
fn contend_lock_nolock(b: &mut test::Bencher) {
    contend::<EmptyTestCase>(b);
}
