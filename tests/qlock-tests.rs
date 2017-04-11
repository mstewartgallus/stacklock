extern crate qlock;

use qlock::{QLock, QLockNode};
use std::sync::Arc;
use std::thread;

#[test]
fn test_as_lock() {
    let lock = Arc::new(QLock::new());

    let mut children = Vec::new();
    for _ in 0..20 {
        let lock_ref = lock.clone();

        let child = thread::spawn(move || {
            for _ in 0..20 {
                let mut node = QLockNode::new();
                let _ = lock_ref.lock(&mut node);
            }
        });
        children.push(child);
    }

    for child in children {
        child.join().unwrap();
    }
}
