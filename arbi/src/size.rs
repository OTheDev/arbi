/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::Assign;
use crate::{Arbi, BitCount, Digit};

impl Arbi {
    /// Return the number of [`Digit`]s used to represent the absolute value of
    /// this integer.
    ///
    /// Instance represents `0` if and only if `size() == 0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Digit};
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size(), 0);
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size(), 1);
    /// a += 1;
    /// assert_eq!(a.size(), 2);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size(&self) -> usize {
        self.vec.len()
    }

    /// Return the number of bits needed to represent the absolute value of this
    /// integer.
    ///
    /// Instance represents `0` if and only if `size_bits() == 0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount, Digit};
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_bits(), 0);
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount);
    /// a += 1;
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount + 1);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size_bits(&self) -> BitCount {
        if self.size() == 0 {
            0
        } else {
            (self.size() as BitCount - 1) * (Digit::BITS as BitCount)
                + Digit::bit_length(*self.vec.last().unwrap()) as BitCount
        }
    }

    /// Return the number of base-`base` digits needed to represent the absolute
    /// value of this integer.
    ///
    /// Instance represents `0` if and only if `size_base() == 0`.
    ///
    /// # Panics
    /// This function will panic if `base` is less than or equal to 1.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_base(10), 0);
    /// let one = Arbi::one();
    /// assert_eq!(one.size_base(10), 1);
    /// let a = Arbi::from_str_radix("123456789", 10).unwrap();
    /// assert_eq!(a.size_base(10), 9);
    /// ```
    ///
    /// Panics on a base less than or equal to 1:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::from(1234);
    /// a.size_base(1);
    /// ```
    pub fn size_base(mut self, base: u32) -> BitCount {
        self.size_base_mut(base)
    }

    /// Return the number of base-`base` digits needed to represent the absolute
    /// value of this integer.
    ///
    /// Instance represents `0` if and only if `size_base_mut() == 0`.
    ///
    /// The value of `self` will compare equal to the return value.
    ///
    /// # Panics
    /// This function will panic if `base` is less than or equal to 1.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut zero = Arbi::zero();
    /// assert_eq!(zero.size_base_mut(10), 0);
    /// assert_eq!(zero, 0);
    /// let mut one = Arbi::one();
    /// assert_eq!(one.size_base_mut(10), 1);
    /// assert_eq!(one, 1);
    /// let mut a = Arbi::from_str_radix("123456789", 10).unwrap();
    /// assert_eq!(a.size_base_mut(10), 9);
    /// assert_eq!(a, 9);
    /// ```
    ///
    /// Panics on a base less than or equal to 1:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(1234);
    /// a.size_base_mut(1);
    /// ```
    pub fn size_base_mut(&mut self, base: u32) -> BitCount {
        if let Some(v) = Self::check_args_size_base(self, base) {
            self.assign(v);
            v
        } else {
            let ret = self.size_radix_no_check(base);
            self.assign(ret);
            ret
        }
    }

    /// Return the number of base-`base` digits needed to represent the absolute
    /// value of this integer.
    ///
    /// Instance represents `0` if and only if `size_base_ref() == 0`.
    ///
    /// # Panics
    /// This function will panic if `base` is less than or equal to 1.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_base_ref(10), 0);
    /// let one = Arbi::one();
    /// assert_eq!(one.size_base_ref(10), 1);
    /// let a = Arbi::from_str_radix("123456789", 10).unwrap();
    /// assert_eq!(a.size_base_ref(10), 9);
    /// ```
    ///
    /// Panics on a base less than or equal to 1:
    /// ```should_panic
    /// use arbi::Arbi;
    /// let a = Arbi::from(1234);
    /// a.size_base_ref(1);
    /// ```
    pub fn size_base_ref(&self, base: u32) -> BitCount {
        if let Some(v) = Self::check_args_size_base(self, base) {
            return v;
        }
        // TODO: what can we achieve without memory allocation?
        let mut clone = self.clone();
        clone.size_radix_no_check(base)
    }

    pub(crate) fn size_radix_no_check(&mut self, base: u32) -> BitCount {
        let mut count: BitCount = 0;
        while self.size() != 0 {
            Self::div_algo_digit_inplace(self, base as Digit);
            count += 1;
        }
        count
    }

    pub(crate) fn check_args_size_base(&self, base: u32) -> Option<BitCount> {
        if base <= 1 {
            panic!("base must be greater than 1: {}", base);
        }
        if self.is_zero() {
            return Some(0);
        }
        if base.is_power_of_two() {
            let bit_length = self.size_bits();
            let base_log2 = u32::ilog2_(base);
            return Some(BitCount::div_ceil_(
                bit_length,
                base_log2 as BitCount,
            ));
        }
        None
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
                    a.size_base_ref(base),
                    a.to_string_radix(base).len() as BitCount
                );

                let r = die_ddigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.size_base_ref(base),
                    a.to_string_radix(base).len() as BitCount
                );

                let r = die_qdigit.sample(&mut rng);
                let a = Arbi::from(r);
                assert_eq!(
                    a.size_base_ref(base),
                    a.to_string_radix(base).len() as BitCount
                );
            }
        }
    }
}

#[cfg(test)]
mod tests_size_bits {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, QDigit};

    #[test]
    fn test_size_bits_returns_0_for_0() {
        assert_eq!(Arbi::zero().size_bits(), 0);
        assert_eq!(
            Arbi::zero().size_bits(),
            (u32::BITS - (0 as u32).leading_zeros()) as BitCount
        );
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let die_s = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_l = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_e = get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for i in 1..u16::MAX {
            assert_eq!(
                Arbi::from(i).size_bits(),
                (u16::BITS - i.leading_zeros()) as BitCount
            );

            let rs = die_s.sample(&mut rng);
            let rl = die_l.sample(&mut rng);
            let re = die_e.sample(&mut rng);

            assert_eq!(
                Arbi::from(rs).size_bits(),
                (Digit::BITS - rs.leading_zeros()) as BitCount
            );
            assert_eq!(
                Arbi::from(rl).size_bits(),
                (DDigit::BITS - rl.leading_zeros()) as BitCount
            );
            assert_eq!(
                Arbi::from(re).size_bits(),
                (QDigit::BITS - re.leading_zeros()) as BitCount
            );
        }
    }

    #[test]
    fn test_size_bits_spec() {
        let (pos, neg, zer, one) =
            (Arbi::from(16), Arbi::from(-16), Arbi::zero(), Arbi::one());

        assert_eq!(pos.size_bits(), 5);
        assert_eq!(neg.size_bits(), 5);
        assert_eq!(zer.size_bits(), 0);
        assert_eq!(one.size_bits(), 1);

        assert_eq!(Arbi::from(u64::MAX).size_bits(), 64);
        assert_eq!(Arbi::from(i64::MIN).size_bits(), 64);
    }
}
