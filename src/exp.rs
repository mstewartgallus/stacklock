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

/// approximates floor(2^(counter * n / max_counter))
#[inline]
pub fn exp(counter: usize, max_counter: usize, n: usize) -> usize {
    let counter_n = counter * n;
    let floor = counter_n / max_counter;
    let ceil = 1 + (counter_n - 1) / max_counter;
    let floor_exp = 1 << floor;
    return floor_exp +
           (((1 << ceil) - floor_exp) * (counter_n - floor * max_counter)) / max_counter;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smoke() {
        let result = exp(128, 200, 8);
        assert_eq!(result, 35);
    }
}
