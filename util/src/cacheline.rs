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
//
use std::ops::{Deref, DerefMut};

#[repr(simd)]
struct Aligner(f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32, f32);

/// Unfortunately repr(align) has not stabilized yet so this is the
/// best we can do.  See
/// https://github.com/rust-lang/rust/issues/33626
pub struct CacheLineAligned<T> {
    _aligner: [Aligner; 0],
    value: T,
}

impl<T> CacheLineAligned<T> {
    #[inline]
    pub fn new(x: T) -> Self {
        CacheLineAligned {
            value: x,
            _aligner: [],
        }
    }
}

impl<T> Deref for CacheLineAligned<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for CacheLineAligned<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}
