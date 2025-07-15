/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use arbi::Arbi;

// Prints the first value in the Fibonacci sequence >= 2**16384.
fn main() {
    let bound = Arbi::one() << 16_384;
    let fib = fib_gte(&bound);
    println!("{fib}");
}

/// Return the first value in the Fibonacci sequence greater than or equal to
/// `bound`.
fn fib_gte(bound: &Arbi) -> Arbi {
    // `a = Arbi::zero()` is fine, but preallocating helps minimize allocations.
    let mut a = Arbi::with_capacity(bound.size() + 1);
    let mut b = Arbi::one();
    while &a < bound {
        let sum = a + &b;
        a = b;
        b = sum;
    }
    a
}
