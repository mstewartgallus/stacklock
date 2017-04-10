#![feature(test)]
extern crate test;
extern crate qlock;

mod contend;

use qlock::{QLock, QLockNode};

use contend::{TestCase, contend};

enum QLockTestCase {}

impl TestCase for QLockTestCase {
    type TestType = QLock;

    fn create_value() -> QLock {
        QLock::new()
    }
    fn do_stuff_with_value(value: &QLock) {
        let mut node = QLockNode::new();
        let _ = value.lock(&mut node);
    }
}

#[bench]
fn contend_lock_qlock(b: &mut test::Bencher) {
    contend::<QLockTestCase>(b);
}
