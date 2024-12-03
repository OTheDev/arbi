/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// Returns `true` if and only if `|self| == 2^k` for some `k`.
    ///
    /// That is, return `true` iff the absolute value of this integer is a power
    /// of 2.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let one = Arbi::from(1);
    /// assert!(one.is_power_of_two());
    /// assert!(1u32.is_power_of_two());
    ///
    /// let two = Arbi::from(2);
    /// assert!(two.is_power_of_two());
    /// assert!(2u32.is_power_of_two());
    ///
    /// let a = Arbi::from(32);
    /// assert!(a.is_power_of_two());
    /// assert!(32u32.is_power_of_two());
    ///
    /// let b = Arbi::from(30);
    /// assert!(!b.is_power_of_two());
    /// assert!(!(30u32.is_power_of_two()));
    ///
    /// let base = Arbi::from(Arbi::BASE);
    /// assert!(base.is_power_of_two());
    /// ```
    pub fn is_power_of_two(&self) -> bool {
        // Integer `k > 0` is a power of two if and only if `k & (k - 1) == 0`.
        // Only one bit should be set in its binary representation.
        let mut count: BitCount = 0;
        for digit in self.vec.iter().rev() {
            count += (*digit).count_ones() as BitCount;
            if count > 1 {
                // > one bit
                return false;
            }
        }
        count == 1
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit, QDigit, SDDigit, SQDigit};

    #[test]
    fn test_is_power_of_two_digit_boundaries() {
        let a = Arbi::from(Digit::MAX);
        assert!(!a.is_power_of_two());
        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert!(a.is_power_of_two());

        let a = Arbi::from(-(Digit::MAX as SDDigit));
        assert!(!a.is_power_of_two());
        let a = Arbi::from(-(Digit::MAX as SDDigit + 1));
        assert!(a.is_power_of_two());

        let a = Arbi::from(DDigit::MAX);
        assert!(!a.is_power_of_two());
        let a = Arbi::from(DDigit::MAX as QDigit + 1);
        assert!(a.is_power_of_two());

        let a = Arbi::from(-(DDigit::MAX as SQDigit));
        assert!(!a.is_power_of_two());
        let a = Arbi::from(-(DDigit::MAX as SQDigit + 1));
        assert!(a.is_power_of_two());
    }

    #[test]
    fn test_is_power_of_two_zero() {
        let a = Arbi::zero();
        assert!(!a.is_power_of_two());
    }

    #[test]
    fn test_is_power_of_two_negative() {
        let a = Arbi::from(-4);
        assert!(a.is_power_of_two());
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_digit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.is_power_of_two(), r.is_power_of_two());

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.is_power_of_two(), r.is_power_of_two());

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.is_power_of_two(), r.is_power_of_two());

            let r = die_sddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.is_power_of_two(), r.unsigned_abs().is_power_of_two());
        }
    }
}
