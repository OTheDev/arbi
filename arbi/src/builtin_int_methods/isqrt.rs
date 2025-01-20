/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Returns the integer part (floor) of the square root of `self`.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt(&self) -> Self {
        if self.is_negative() {
            panic!("argument of isqrt() cannot be negative")
        } else if self.is_zero() {
            Arbi::zero()
        } else {
            // TODO
            unimplemented!()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    #[should_panic = "argument of isqrt() cannot be negative"]
    fn test_negative_panics() {
        let _ = Arbi::from(-1).isqrt();
    }

    #[test]
    fn test_isqrt_0_is_0() {
        assert_eq!(Arbi::zero().isqrt(), 0);
    }
}
