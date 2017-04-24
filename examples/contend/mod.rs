use std::thread;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Barrier};

use criterion::Bencher;

pub trait TestCase {
    type TestType: Clone + Send;

    fn create_value() -> Self::TestType;
    fn do_stuff_with_value(value: &Self::TestType, times: usize);
}

pub fn contend<T: TestCase + 'static>(b: &mut Bencher) {
    let lock: T::TestType = T::create_value();

    let mut children = Vec::new();

    let num = 20;

    let is_done = Arc::new(AtomicBool::new(false));
    let start = Arc::new(Barrier::new(num + 1));
    let done = Arc::new(Barrier::new(num + 1));

    for _ in 0..num {
        let lock_ref = lock.clone();
        let start_ref = start.clone();
        let done_ref = done.clone();
        let is_done_ref = is_done.clone();

        let child = thread::spawn(move || {
            loop {
                start_ref.wait();
                if is_done_ref.load(Ordering::Acquire) {
                    break;
                }

                T::do_stuff_with_value(&lock_ref, 100);

                done_ref.wait();
            }
        });
        children.push(child);
    }

    b.iter(|| {
        start.wait();
        done.wait();
    });
    is_done.store(true, Ordering::Release);
    start.wait();

    for child in children {
        child.join().unwrap();
    }
}
