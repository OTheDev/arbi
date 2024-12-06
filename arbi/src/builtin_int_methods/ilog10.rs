/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(10);
    /// assert_eq!(a.ilog10(), 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// zero.ilog10();
    /// ```
    ///
    /// ```should_panic
    /// use arbi::Arbi;
    /// let minus_one = Arbi::from(-1);
    /// minus_one.ilog10();
    /// ```
    pub fn ilog10(self) -> BitCount {
        self.ilog(10)
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// The value of `self` will compare equal to the return value.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(10);
    /// assert_eq!(a.ilog10_mut(), 1);
    /// assert_eq!(a, 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut zero = Arbi::zero();
    /// zero.ilog10_mut();
    /// ```
    ///
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut minus_one = Arbi::from(-1);
    /// minus_one.ilog10_mut();
    /// ```
    pub fn ilog10_mut(&mut self) -> BitCount {
        self.ilog_mut(10)
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(10);
    /// assert_eq!(a.ilog10_ref(), 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// zero.ilog10_ref();
    /// ```
    ///
    /// ```should_panic
    /// use arbi::Arbi;
    /// let minus_one = Arbi::from(-1);
    /// minus_one.ilog10_ref();
    /// ```
    pub fn ilog10_ref(&self) -> BitCount {
        self.ilog_ref(10)
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, BitCount, DDigit, Digit, QDigit};

    #[test]
    fn test_digit_boundaries() {
        let a = Arbi::from(Digit::MAX);
        assert_eq!(a.ilog10(), Digit::MAX.ilog10() as BitCount);
        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(a.ilog10(), (Digit::MAX as DDigit + 1).ilog10() as BitCount);

        let a = Arbi::from(DDigit::MAX);
        assert_eq!(a.ilog10(), DDigit::MAX.ilog10() as BitCount);
        let a = Arbi::from(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.ilog10(),
            (DDigit::MAX as QDigit + 1).ilog10() as BitCount
        );
    }

    #[test]
    #[should_panic = "self must be positive: 0"]
    fn test_zero() {
        let a = Arbi::zero();
        a.ilog10();
    }

    #[test]
    #[should_panic = "self must be positive: -4"]
    fn test_is_power_of_two_negative() {
        let a = Arbi::from(-4);
        a.ilog10();
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
            if r == 0 {
                continue;
            }
            let a = Arbi::from(r);
            assert_eq!(a.ilog10(), r.ilog10() as BitCount);

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.ilog10(), r.ilog10() as BitCount);

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.ilog10(), r.ilog10() as BitCount);
        }
    }
}
