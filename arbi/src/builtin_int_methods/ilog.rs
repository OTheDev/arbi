/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// Returns the base-`base` logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero, or if
    /// `base` is less than 2.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(10);
    /// assert_eq!(a.ilog(8), 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// zero.ilog(8);
    /// ```
    ///
    /// ```should_panic
    /// use arbi::Arbi;
    /// let minus_one = Arbi::neg_one();
    /// minus_one.ilog(8);
    /// ```
    ///
    /// A base less than 2 causes a panic
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::from(4);
    /// a.ilog(1);
    /// ```
    pub fn ilog(self, base: u32) -> BitCount {
        Self::check_ilog_args(&self, base);
        self.size_base(base) - 1
    }

    /// Returns the base-`base` logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero, or if
    /// `base` is less than 2.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(10);
    /// a.ilog_mut(8);
    /// assert_eq!(a, 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut zero = Arbi::zero();
    /// zero.ilog_mut(8);
    /// ```
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut minus_one = Arbi::neg_one();
    /// minus_one.ilog_mut(8);
    /// ```
    ///
    /// A base less than 2 causes a panic
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(4);
    /// a.ilog_mut(1);
    /// ```
    pub fn ilog_mut(&mut self, base: u32) -> BitCount {
        Self::check_ilog_args(self, base);
        let ret = self.size_base_mut(base) - 1;
        self.decr();
        ret
    }

    /// Returns the base-`base` logarithm of the number, rounded down.
    ///
    /// # Panics
    /// This function will panic if `self` is less than or equal to zero, or if
    /// `base` is less than 2.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(10);
    /// assert_eq!(a.ilog_ref(8), 1);
    /// ```
    ///
    /// Nonpositive values panic:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// zero.ilog_ref(8);
    /// ```
    /// ```should_panic
    /// use arbi::Arbi;
    /// let minus_one = Arbi::neg_one();
    /// minus_one.ilog_ref(8);
    /// ```
    ///
    /// A base less than 2 causes a panic
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::from(4);
    /// a.ilog_ref(1);
    /// ```
    pub fn ilog_ref(&self, base: u32) -> BitCount {
        Self::check_ilog_args(self, base);
        self.size_base_ref(base) - 1
    }

    fn check_ilog_args(x: &Self, base: u32) {
        if x <= 0 {
            panic!("self must be positive: {}", x);
        }
        if base < 2 {
            panic!("base must be greater than or equal to 2: {}", base);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, BitCount, DDigit, Digit, QDigit};

    #[test]
    fn test_digit_boundaries() {
        for base in 2u32..=36u32 {
            let a = Arbi::from(Digit::MAX);
            assert_eq!(a.ilog_ref(base), Digit::MAX.ilog(base) as BitCount);
            let a = Arbi::from(Digit::MAX as DDigit + 1);
            assert_eq!(
                a.ilog_ref(base),
                (Digit::MAX as DDigit + 1).ilog(base as DDigit) as BitCount
            );

            let a = Arbi::from(DDigit::MAX);
            assert_eq!(
                a.ilog_ref(base),
                DDigit::MAX.ilog(base as DDigit) as BitCount
            );
            let a = Arbi::from(DDigit::MAX as QDigit + 1);
            assert_eq!(
                a.ilog_ref(base),
                (DDigit::MAX as QDigit + 1).ilog(base as QDigit) as BitCount
            );
        }
    }

    #[test]
    #[should_panic = "self must be positive: 0"]
    fn test_zero() {
        let a = Arbi::zero();
        a.ilog_ref(8);
    }

    #[test]
    #[should_panic = "self must be positive: -4"]
    fn test_is_power_of_two_negative() {
        let a = Arbi::from(-4);
        a.ilog_ref(8);
    }

    #[test]
    #[should_panic = "base must be greater than or equal to 2: 0"]
    fn test_invalid_base() {
        let a = Arbi::from(4);
        a.ilog_ref(0);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for base in 2u32..=36u32 {
            for _ in 0..i16::MAX {
                let r = die_digit.sample(&mut rng);
                if r == 0 {
                    continue;
                }
                let a = Arbi::from(r);
                assert_eq!(a.ilog_ref(base), r.ilog(base) as BitCount);

                let r = die_ddigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.ilog_ref(base),
                    r.ilog(base as DDigit) as BitCount
                );

                let r = die_qdigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.ilog_ref(base),
                    r.ilog(base as QDigit) as BitCount
                );
            }
        }
    }
}
