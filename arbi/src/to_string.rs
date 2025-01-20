/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::from_string::configs::BASE_MBS;
use crate::Base;
use crate::BitCount;
use crate::{Arbi, Digit, DBL_MAX_INT};
use alloc::string::String;
use core::convert::TryInto;

/// `LOG_BASE_2[base]` gives \\( \log_{base}2 \\) (with some rounding up).
pub(crate) const LOG_BASE_2: [f64; 37] = [
    0.0, 0.0, 1.0, 0.631, 0.5, 0.431, 0.387, 0.357, 0.334, 0.316, 0.302, 0.290,
    0.279, 0.271, 0.263, 0.256, 0.25, 0.245, 0.240, 0.236, 0.232, 0.228, 0.225,
    0.222, 0.219, 0.216, 0.213, 0.211, 0.209, 0.206, 0.204, 0.202, 0.200,
    0.199, 0.197, 0.195, 0.194,
];

impl Arbi {
    //  In the documentation block above `base_length()`, it is shown how to
    //  calculate the minimum number of base-b digits, \\( n \\), required to
    //  represent any integer with \\( m \\) base-c digits.
    //
    //  We can find an upper bound another way as well.
    //
    //  Let \\( e \\) denote the largest exponent such that \\( c^{e} \\) fits
    //  in one base-b digit. By construction, any e-digit base-c number will fit
    //  in a base-b digit, but not every \\( (e + 1) \\) digit base-c number
    //  will. By dividing the number of base-c digits in an integer, \\( m \\),
    //  by \\( e \\), and rounding up the result of the division to the nearest
    //  integer, we obtain an upperbound on the number of base-b digits, \\( n
    //  \\), needed to represent any m-digit base-c integer.

    /// Return an estimate of the number of base-`base` digits required to
    /// represent this integer.
    ///
    /// Given an n-digit integer in base b, the largest integer representable is
    /// \\[
    ///     b^{n} - 1
    /// \\]
    ///
    /// The minimum number of base b digits, n, required to represent any
    /// m-digit base c integer is such that:
    /// \\[
    /// \begin{align}
    ///     b^{n} - 1                 & \geq c^{m} - 1                      \\\\
    ///     b^{n}                     & \geq c^{m}                          \\\\
    ///     \frac{b^{n}}{c^{m}}       & \geq 1                              \\\\
    ///     \log(b^{n}) - \log(c^{m}) & \geq 0                              \\\\
    ///     n                         & \geq m \cdot \frac{\log(c)}{\log(b)}
    /// \end{align}
    /// \\]
    ///
    /// Use
    /// \\[
    ///     n = \left\lceil m \cdot \frac{\log(c)}{\log(b)} \right\rceil
    /// \\]
    ///
    /// For example, the minimum number of base 10 digits required to represent
    /// any m-digit base 2 integer is:
    /// \\[
    ///     n = \left\lceil m * \log_{10}(2) \right\rceil
    /// \\]
    /// If `x` has bit length less than or equal to 2 ** 53, return an estimate
    /// of the number of base-`base` digits needed to represent the absolute
    /// value of this integer. Otherwise, return the exact number of base-`base`
    /// digits.
    fn base_length(x: &Self, base: usize) -> BitCount {
        // TODO: analyze
        if x == 0 {
            return 1;
        }
        let bitlen: BitCount = x.size_bits();
        if bitlen as BitCount > DBL_MAX_INT as BitCount {
            // TODO: find some quick upperbound.
            // let ilog2_base = base.ilog2();
            // (x.size_bits() - 1) / (ilog2_base as BitCount) + (1 as BitCount)
            x.size_base_ref(base as u32)
        } else {
            // This is much more efficient than using size_base()
            crate::floor::floor(bitlen as f64 * LOG_BASE_2[base] + 1.0)
                as BitCount
        }
    }

    pub(crate) fn to_string_base_(
        &self,
        base: Base,
        lowercase: bool,
    ) -> String {
        let base: usize = base.value() as usize;
        assert!((2..=36).contains(&base));

        const BASE_DIGITS_LOWER: &str = "0123456789abcdefghijklmnopqrstuvwxyz";
        const BASE_DIGITS_UPPER: &str = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

        let base_digits = if lowercase {
            BASE_DIGITS_LOWER
        } else {
            BASE_DIGITS_UPPER
        };

        if self.size() == 0 {
            return "0".into();
        }

        let mut result = String::new();
        let true_estimate: BitCount =
            Self::base_length(self, base) + BitCount::from(self.neg);
        let estimate: usize = if true_estimate > usize::MAX as BitCount {
            let exact =
                self.size_base_ref(base as u32) + BitCount::from(self.neg);
            assert!(exact > isize::MAX as BitCount);
            panic!(
                "Base-{} digit estimation exceeds isize::MAX bytes. Exact = {}",
                base, exact
            );
        } else {
            true_estimate.try_into().unwrap()
        };
        result.reserve(estimate);
        // let exact_chars =
        //     self.size_base(base as u32) + if self.neg { 1 } else { 0 };
        // let exact_chars_usize = if exact_chars > usize::MAX as BitCount {
        //     panic!(
        //         "More than usize::MAX bytes needed. Arbi = {}, base = {}",
        //         self, base
        //     );
        // } else {
        //     exact_chars.try_into().unwrap()
        // };
        // result.reserve(exact_chars_usize);

        let basembs = BASE_MBS[base];
        let max_batch_size = basembs.mbs;
        let divisor = basembs.base_pow_mbs;
        let mut copy = self.clone();
        while copy.size() != 0 {
            let mut remainder: Digit =
                Self::div_algo_digit_inplace(&mut copy, divisor);
            for _ in 0..max_batch_size {
                if remainder == 0 && copy.size() == 0 {
                    break;
                }

                let current_digit: Digit = remainder % base as Digit;
                remainder /= base as Digit;

                result.push(
                    base_digits.chars().nth(current_digit as usize).unwrap(),
                );
            }
        }

        if self.neg {
            result.push('-');
        }

        result.chars().rev().collect::<String>()
    }

    /// Return a [`String`] containing the base-`base` representation of the
    /// integer, where `base` must be an integer in \\( [2, 36] \\).
    ///
    /// # Examples
    /// ```
    /// use arbi::{
    ///     base::{DEC, HEX},
    ///     Arbi,
    /// };
    /// assert_eq!(Arbi::from(123456789).to_string_base(DEC), "123456789");
    /// assert_eq!(Arbi::from(123456789).to_string_base(HEX), "75bcd15");
    /// assert_eq!(Arbi::from(-123456789).to_string_base(HEX), "-75bcd15");
    /// ```
    pub fn to_string_base(&self, base: Base) -> String {
        self.to_string_base_(base, true)
    }

    /// Equivalent to [`Arbi::to_string_base()`], but panics if the base is
    /// invalid (i.e. not in \\( [2, 36] \\)).
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Base};
    ///
    /// let a = Arbi::from(123456789);
    /// let s = a.to_string_radix(10);
    /// assert_eq!(s, "123456789");
    /// ```
    pub fn to_string_radix(&self, radix: u32) -> String {
        let base: Base = match radix.try_into() {
            Err(_) => panic!("`radix` is not an integer in [2, 36]"),
            Ok(b) => b,
        };

        self.to_string_base(base)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::util::test::{get_uniform_die, BASE10};
    use crate::{QDigit, SQDigit};

    pub(crate) trait ToStringBase {
        fn to_string_base(&self, base: Base) -> String;
    }

    macro_rules! impl_to_string_base {
        ($($signed:ty => $unsigned:ty),*) => {
            $(

    /* !impl_to_string_base_signed */
    impl ToStringBase for $signed {
        #[allow(unused_comparisons)]
        fn to_string_base(&self, base: Base) -> String {
            use alloc::string::ToString;

            let base = u32::from(base);

            let mut num: $unsigned = if *self < 0 {
                (0 as $unsigned).wrapping_sub((*self) as $unsigned)
            } else {
                (*self) as $unsigned
            };

            if num == 0 {
                return "0".to_string();
            }

            let mut result = String::new();
            let negative = *self < 0;

            while num > 0 {
                let rem = (num % base as $unsigned) as u8;
                result.push(if rem < 10 {
                    (b'0' + rem) as char
                } else {
                    (b'a' + rem - 10) as char
                });
                num /= base as $unsigned;
            }

            if negative {
                result.push('-');
            }

            result.chars().rev().collect()
        }
    }

            )+
        };
    }
    /* impl_to_string_base_signed! */

    impl_to_string_base!(
        i8 => u8,
        i16 => u16,
        i32 => u32,
        i64 => u64,
        i128 => u128,
        isize => usize,
        u8 => u8,
        u16 => u16,
        u32 => u32,
        u64 => u64,
        u128 => u128,
        usize => usize
    );

    #[test]
    fn test_to_string_large() {
        let large_integer = "3402823669209384634633746074317682114553423908104";
        let arbi = Arbi::from_str_base(large_integer, BASE10).unwrap();
        let as_string = arbi.to_string_base(BASE10);

        assert_eq!(as_string, large_integer);
    }

    use crate::util::test::{get_seedable_rng, Distribution};
    use crate::{DDigit, Digit, SDDigit, SDigit};

    fn test_to_string_base(b: usize) {
        let b: Base = b.try_into().unwrap();

        assert_eq!(Arbi::zero().to_string_base(b), 0.to_string_base(b));
        assert_eq!(
            Arbi::from(Digit::MAX).to_string_base(b),
            Digit::MAX.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(DDigit::MAX).to_string_base(b),
            DDigit::MAX.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SDigit::MIN).to_string_base(b),
            SDigit::MIN.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SDigit::MAX).to_string_base(b),
            SDigit::MAX.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SDDigit::MIN).to_string_base(b),
            SDDigit::MIN.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SDDigit::MAX).to_string_base(b),
            SDDigit::MAX.to_string_base(b)
        );
        assert_eq!(
            Arbi::from(-(Digit::MAX as SDDigit))
                .to_string_base(b.try_into().unwrap()),
            (-(Digit::MAX as SDDigit)).to_string_base(b)
        );
        assert_eq!(
            Arbi::from(Digit::MAX as DDigit + 1)
                .to_string_base(b.try_into().unwrap()),
            (Digit::MAX as DDigit + 1).to_string_base(b)
        );
        assert_eq!(
            Arbi::from(QDigit::MAX).to_string_base(b),
            (QDigit::MAX).to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SQDigit::MIN).to_string_base(b),
            (SQDigit::MIN).to_string_base(b)
        );
        assert_eq!(
            Arbi::from(SQDigit::MAX).to_string_base(b),
            (SQDigit::MAX).to_string_base(b)
        );

        let (mut rng, _) = get_seedable_rng();
        let udist = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        let udist_digit = get_uniform_die(Digit::MIN, Digit::MAX);

        let mn = i16::MIN / 8;
        let mx = i16::MAX / 8;
        for i in mn..mx {
            let r: SQDigit = udist.sample(&mut rng);
            let r_digit: Digit = udist_digit.sample(&mut rng);
            assert_eq!(Arbi::from(r).to_string_base(b), r.to_string_base(b));
            assert_eq!(
                Arbi::from(r_digit).to_string_base(b),
                r_digit.to_string_base(b)
            );
            assert_eq!(Arbi::from(i).to_string_base(b), i.to_string_base(b));
        }
    }

    #[test]
    fn test_to_string() {
        // Test valid bases
        for base in 2..=36 {
            test_to_string_base(base);
        }
    }
}
