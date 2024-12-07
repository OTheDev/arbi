/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount};
    ///
    /// let a = Arbi::from(2);
    /// assert_eq!(a.ilog2(), 1);
    /// assert_eq!(2_i32.ilog2(), 1);
    ///
    /// let b = Arbi::from(123456789_i32);
    /// assert_eq!(b.ilog2(), 26);
    /// assert_eq!(123456789_i32.ilog2(), 26);
    ///
    /// let c = Arbi::from(u128::MAX);
    /// assert_eq!(c.ilog2(), u128::MAX.ilog2() as BitCount);
    /// ```
    ///
    /// This function will panic if `self` is zero or negative:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::zero();
    /// a.ilog2();
    /// ```
    ///
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::neg_one();
    /// a.ilog2();
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    pub fn ilog2(&self) -> BitCount {
        if self <= 0 {
            panic!("self must be positive: {}", self)
        }
        self.size_bits() - 1
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, BitCount, DDigit, Digit, QDigit};

    #[test]
    fn test_digit_boundaries() {
        let a = Arbi::from(Digit::MAX);
        assert_eq!(a.ilog2(), Digit::MAX.ilog2() as BitCount);
        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(a.ilog2(), (Digit::MAX as DDigit + 1).ilog2() as BitCount);

        let a = Arbi::from(DDigit::MAX);
        assert_eq!(a.ilog2(), DDigit::MAX.ilog2() as BitCount);
        let a = Arbi::from(DDigit::MAX as QDigit + 1);
        assert_eq!(a.ilog2(), (DDigit::MAX as QDigit + 1).ilog2() as BitCount);
    }

    #[test]
    #[should_panic = "self must be positive: 0"]
    fn test_zero() {
        let a = Arbi::zero();
        a.ilog2();
    }

    #[test]
    #[should_panic = "self must be positive: -4"]
    fn test_is_power_of_two_negative() {
        let a = Arbi::from(-4);
        a.ilog2();
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_digit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.ilog2(), r.ilog2() as BitCount);

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.ilog2(), r.ilog2() as BitCount);

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.ilog2(), r.ilog2() as BitCount);
        }
    }
}
