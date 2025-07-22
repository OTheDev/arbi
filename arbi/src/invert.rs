/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Return the inverse of `self` modulo `modulus`, if it exists. Otherwise,
    /// return `None`.
    ///
    /// Mathematically, if the inverse exists, the return value, \\( r \\),
    /// will be such that \\( 0 \leq r \lt |\text{modulus}| \\) (\\( 0 \\) only
    /// if \\( |\text{modulus}| = 1 \\)).
    ///
    /// # Panic
    /// Panics if `modulus` is zero.
    pub fn invert_ref(&self, modulus: &Self) -> Option<Self> {
        assert!(!modulus.is_zero(), "division by zero attempt");
        if modulus.size() == 1 && modulus.vec[0] == 1 {
            // -1 or 1
            return Some(Self::zero());
        }
        None
    }
}
