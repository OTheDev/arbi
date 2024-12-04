/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount, Digit};

impl Arbi {
    /// Test bit `i` (zero-based indexing) of the absolute value of this
    /// integer.
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
    pub fn test_bit(&self, i: BitCount) -> bool {
        let digit_idx: usize = (i / Digit::BITS as BitCount) as usize;
        if self.size() <= digit_idx {
            false
        } else {
            ((self.vec[digit_idx] >> (i % Digit::BITS as BitCount)) & 1) != 0
        }
    }

    /// Set bit `i` (zero-based indexing) of the absolute value of this integer,
    /// leaving its sign unchanged.
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
    pub fn set_bit(&mut self, i: BitCount) -> &mut Self {
        let digit_idx: usize = (i / Digit::BITS as BitCount) as usize;
        if digit_idx >= self.vec.len() {
            self.vec.resize(digit_idx + 1, 0);
        }
        self.vec[digit_idx] |= (1 as Digit) << (i % Digit::BITS as BitCount);
        self
    }

    /// Clear bit `i` (zero-based indexing) of the absolute value of this
    /// integer, leaving its sign unchanged (unless it becomes zero from a
    /// negative `self`).
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // 11000000111001 (absolute value of -12345)
    /// let mut a = Arbi::from(-12345);
    ///
    /// a.clear_bit(0);
    /// // 11000000111000
    /// assert_eq!(a, -12344);
    ///
    /// a.clear_bit(13);
    /// // 1000000111000
    /// assert_eq!(a, -4152);
    /// ```
    ///
    /// ## Complexity
    /// - \\( O(1) \\) when clearing an existing bit.
    /// - \\( O(n) \\) when clearing a bit outside the current bit width, as
    ///     this requires resizing.
    pub fn clear_bit(&mut self, i: BitCount) {
        let n: usize = self.size();
        let digit_idx: usize = (i / Digit::BITS as BitCount) as usize;
        if digit_idx < n {
            self.vec[digit_idx] &=
                !((1 as Digit) << (i % Digit::BITS as BitCount));
            self.trim();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{BitCount, DDigit, QDigit};

    #[test]
    fn test_clear_and_set_bit_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(0, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let mut r = die_digit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.bit_length() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as Digit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as Digit) << (i as BitCount);
            assert_eq!(a, r);

            let mut r = die_ddigit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.bit_length() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as DDigit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as DDigit) << (i as BitCount);
            assert_eq!(a, r);

            let mut r = die_qdigit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.bit_length() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as QDigit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as QDigit) << (i as BitCount);
            assert_eq!(a, r);
        }
    }

    #[test]
    fn test_clear_bit() {
        assert_eq!(Arbi::zero().set_bit(0), 1);
        assert_eq!(Arbi::from(10).set_bit(2), 14);

        for i in 0..=53 {
            let mut a = Arbi::from(2.0_f64.powi(i as i32));
            a.clear_bit(i as BitCount);
            assert_eq!(a, 0);
        }
    }

    #[test]
    fn test_set_and_test_bit() {
        assert_eq!(Arbi::zero().set_bit(0), 1);
        assert_eq!(Arbi::from(10).set_bit(2), 14);

        for i in 0..=53 {
            let mut a = Arbi::zero();
            a.set_bit(i as BitCount);
            assert_eq!(a, (2.0_f64.powi(i as i32)));
            assert!(a.test_bit(i as BitCount));
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
