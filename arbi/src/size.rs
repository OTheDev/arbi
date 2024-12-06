/*
Copyright 2024 Owain Davies
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
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size(), 0);
    ///
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size(), 1);
    ///
    /// a.incr();
    /// assert_eq!(a.size(), 2);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size(&self) -> usize {
        self.vec.len()
    }

    /// Return the number of bits used to represent the absolute value of this
    /// integer.
    ///
    /// Instance represents `0` if and only if `size_bits() == 0`.
    ///
    /// This is equivalent to [`Arbi::bit_length()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount, Digit};
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_bits(), 0);
    ///
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount);
    ///
    /// a.incr();
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount + 1);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size_bits(&self) -> BitCount {
        self.bit_length()
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
    /// let one = Arbi::from(1);
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
    ///
    /// let mut zero = Arbi::zero();
    /// assert_eq!(zero.size_base_mut(10), 0);
    /// assert_eq!(zero, 0);
    ///
    /// let mut one = Arbi::from(1);
    /// assert_eq!(one.size_base_mut(10), 1);
    /// assert_eq!(one, 1);
    ///
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
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_base_ref(10), 0);
    ///
    /// let one = Arbi::from(1);
    /// assert_eq!(one.size_base_ref(10), 1);
    ///
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
        while self > 0 {
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
            let bit_length = self.bit_length();
            let base_log2 = base.ilog2();
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
