// Copyright 2017 Steven Stewart-Gallus
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
// implied.  See the License for the specific language governing
// permissions and limitations under the License.
use std::ptr;
use std::cell::UnsafeCell;

use stack::{NonatomicStack, Stack};
pub use stack::Node;

/// Multiple producer, single consumer queue
pub struct Queue {
    inbox: Stack,
    outbox: UnsafeCell<NonatomicStack>,
}

impl Queue {
    #[inline(always)]
    pub fn new() -> Queue {
        Queue {
            inbox: Stack::new(),
            outbox: UnsafeCell::new(NonatomicStack::new()),
        }
    }

    pub unsafe fn enqueue(&self, node: *mut Node) {
        self.inbox.push(node);
    }

    pub unsafe fn dequeue(&self) -> *mut Node {
        let outbox = &mut *self.outbox.get();

        let mut popped = outbox.pop();
        if popped != ptr::null_mut() {
            return popped;
        }

        let mut new_outbox = self.inbox.drain().reverse();

        popped = new_outbox.pop();

        *outbox = new_outbox;

        return popped;
    }
}
