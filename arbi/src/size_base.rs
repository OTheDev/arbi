/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::{Arbi, BitCount};

impl Arbi {
    /// If nonzero, return the number of digits in base `base > 1` needed to
    /// represent the absolute value of this integer. Otherwise, return `0`.
    ///
    /// # Panics
    /// This function will panic if `base` is less than or equal to 1.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_base(10), 0);
    ///
    /// let one = Arbi::from(1);
    /// assert_eq!(one.size_base(10), 1);
    ///
    /// let a = Arbi::from_str_radix("123456789", 10).unwrap();
    /// assert_eq!(a.size_base(10), 9);
    /// ```
    pub fn size_base(&self, base: u32) -> BitCount {
        if base <= 1 {
            panic!("base must be greater than 1: {}", base);
        }
        if self.is_zero() {
            return 0;
        }
        if base.is_power_of_two() {
            let bit_length = self.bit_length();
            let base_log2 = base.ilog2();
            return BitCount::div_ceil_(bit_length, base_log2 as BitCount);
        }
        use crate::Digit;
        let mut count: BitCount = 0;
        // TODO: what can we achieve without memory allocation?
        let mut clone = self.clone();
        while clone > 0 {
            Self::div_algo_digit_inplace(&mut clone, base as Digit);
            count += 1;
        }
        count
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, BitCount, DDigit, Digit, QDigit};
    use alloc::string::ToString;

    #[test]
    fn test_digit_boundaries() {
        let a = Arbi::from(Digit::MAX);
        assert_eq!(a.size_base(10), Digit::MAX.to_string().len() as BitCount);
        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(
            a.size_base(10),
            (Digit::MAX as DDigit + 1).to_string().len() as BitCount
        );

        let a = Arbi::from(DDigit::MAX);
        assert_eq!(a.size_base(10), DDigit::MAX.to_string().len() as BitCount);
        let a = Arbi::from(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.size_base(10),
            (DDigit::MAX as QDigit + 1).to_string().len() as BitCount
        );
    }

    #[test]
    #[should_panic = "base must be greater than 1: 0"]
    fn test_panic_on_base_0() {
        let a = Arbi::from(1234);
        a.size_base(0);
    }

    #[test]
    fn test_zero() {
        let zero = Arbi::zero();
        assert_eq!(zero.size_base(10), 0);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for base in 2..=36 {
            for _ in 0..i16::MAX {
                let r = die_digit.sample(&mut rng);
                if r == 0 {
                    continue;
                }
                let a = Arbi::from(r);
                assert_eq!(
                    a.size_base(base),
                    a.to_string_radix(base).len() as BitCount
                );

                let r = die_ddigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.size_base(base),
                    a.to_string_radix(base).len() as BitCount
                );

                let r = die_qdigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.size_base(base),
                    a.to_string_radix(base).len() as BitCount
                );
            }
        }
    }
}
