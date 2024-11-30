/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

impl Arbi {
    /// Test bit `i` (zero-based indexing), acting as if the integer is
    /// nonnegative.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // 11000000111001
    /// let a = Arbi::from(12345);
    /// assert_eq!(a.test_bit(0), true);
    /// assert_eq!(a.test_bit(1), false);
    /// assert_eq!(a.test_bit(5), true);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    pub fn test_bit(&self, i: usize) -> bool {
        let digit_idx: usize = i / Digit::BITS as usize;

        if self.size() <= digit_idx {
            false
        } else {
            ((self.vec[digit_idx] >> (i % Digit::BITS as usize)) & 1) != 0
        }
    }

    /// Set bit `i` (zero-based indexing), acting as if the integer is
    /// nonnegative, but preserving its original sign in the result.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // 11000000111001
    /// let mut a = Arbi::from(12345);
    ///
    /// a.set_bit(1);
    /// // 11000000111011
    /// assert_eq!(a, 12347);
    ///
    /// a.set_bit(14);
    /// // 111000000111011
    /// assert_eq!(a, 28731);
    /// ```
    ///
    /// ## Complexity
    /// - \\( O(1) \\) when setting an existing bit.
    /// - \\( O(n) \\) when setting a bit outside the current bit width, as
    ///     this requires resizing.
    pub fn set_bit(&mut self, i: usize) -> &mut Self {
        let n: usize = self.size();
        let digit_idx: usize = i / Digit::BITS as usize;

        if digit_idx < n {
            self.vec[digit_idx] |= (1 as Digit) << (i % Digit::BITS as usize);
        } else {
            self.vec.resize(digit_idx + 1, 0);
            self.vec[n..digit_idx].fill(0);
            self.vec[digit_idx] = (1 as Digit) << (i % Digit::BITS as usize);
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_bit() {
        assert_eq!(Arbi::zero().set_bit(0), 1);
        assert_eq!(Arbi::from(10).set_bit(2), 14);

        for i in 0..(Digit::BITS) {
            assert_eq!(
                Arbi::zero().set_bit(i as usize),
                (2.0_f64.powi(i as i32)) as Digit
            );
        }
    }

    #[test]
    fn test_test_bit() {
        // Zero
        let x = Arbi::zero();
        assert_eq!(x.test_bit(0), false);
        assert_eq!(x.test_bit(42040), false);

        // One
        let x = Arbi::from(1);
        assert_eq!(x.test_bit(0), true);
        assert_eq!(x.test_bit(1), false);

        // 1010 (MSB is the 1)
        let x = Arbi::from(10);
        assert_eq!(x.test_bit(0), false);
        assert_eq!(x.test_bit(1), true);
        assert_eq!(x.test_bit(2), false);
        assert_eq!(x.test_bit(3), true);

        // Powers of Two
        let mut one = Arbi::from(1);
        one <<= 1_usize;
        for i in 1..65000 {
            assert_eq!(one.test_bit(i - 1), false);
            assert_eq!(one.test_bit(i), true, "Failure at i = {}", i);
            assert_eq!(one.test_bit(i + 1), false);
            one <<= 1_usize;
        }
    }
}
