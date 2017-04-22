#![feature(test)]
extern crate test;

mod contend;

extern crate qlock_util;

use std::mem;
use std::boxed::Box;
use std::sync::mpsc;
use std::sync::mpsc::{Receiver, Sender};
use std::thread;

use contend::{TestCase, contend};

// This is like a lock but instead of locking we bunch things to do up
// in a queue.

struct Lock {
    sender: Sender<Box<Thunk>>,
}

trait Thunk: Send {
    fn run(&mut self);
}

impl Clone for Lock {
    fn clone(&self) -> Self {
        Lock { sender: self.sender.clone() }
    }
}

impl Lock {
    #[inline(never)]
    fn new() -> Lock {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let myreceiver: Receiver<Box<Thunk>> = receiver;
            loop {
                let mut thunk: Box<Thunk> = match myreceiver.recv() {
                    Err(_) => break,
                    Ok(x) => x,
                };
                thunk.run()
            }
        });
        Lock { sender: sender }
    }

    #[inline(never)]
    fn forward<F: Send + 'static>(&self, f: F)
        where F: FnOnce()
    {
        struct ThunkImpl<F> {
            f: Option<F>,
        };
        impl<F: Send> Thunk for ThunkImpl<F>
            where F: FnOnce()
        {
            fn run(&mut self) {
                let mut result = None;
                mem::swap(&mut self.f, &mut result);
                (result.unwrap())();
            }
        }
        self.sender.send(Box::new(ThunkImpl { f: Some(f) })).unwrap();
    }
}

enum LockTestCase {}

impl TestCase for LockTestCase {
    type TestType = Lock;

    fn create_value() -> Self::TestType {
        Lock::new()
    }
    fn do_stuff_with_value(value: &Self::TestType) {
        value.forward(move || {
        });
    }
}

#[bench]
fn contend_lock_forwarding(b: &mut test::Bencher) {
    contend::<LockTestCase>(b);
}
