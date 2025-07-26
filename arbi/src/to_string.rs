/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::from_string::configs::BASE_MBS;
use crate::Base;
use crate::{Arbi, Digit};
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::TryInto;

const BASE_DIGITS_LOWER_BYTES: &[u8; 36] =
    b"0123456789abcdefghijklmnopqrstuvwxyz";
const BASE_DIGITS_UPPER_BYTES: &[u8; 36] =
    b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";

impl Arbi {
    fn to_string_base_pow2(&self, base: Base, lowercase: bool) -> String {
        debug_assert!(base.value().is_power_of_two());

        let base_digits = if lowercase {
            BASE_DIGITS_LOWER_BYTES
        } else {
            BASE_DIGITS_UPPER_BYTES
        };

        if self.is_zero() {
            return "0".into();
        }

        let capacity = self
            .size_base_ref(base.value() as u32)
            .try_into()
            .unwrap_or(usize::MAX)
            .saturating_add(usize::from(self.is_negative()));
        let mut bytes: Vec<u8> = Vec::new();
        bytes.reserve_exact(capacity);

        #[cfg(debug_assertions)]
        let initial_capacity = bytes.capacity();

        let base_digit_bits = base.value().trailing_zeros();
        let base_digit_mask = ((1 as Digit) << base_digit_bits) - 1;

        if matches!(base.value(), 2 | 4 | 16) {
            debug_assert!(Digit::BITS % base.value().trailing_zeros() == 0);
            self.process_digits_base_pow2_aligned(
                &mut bytes,
                base_digit_bits,
                base_digit_mask,
                base_digits,
                true,
            );
        } else {
            self.process_digits_base_pow2_generic(
                &mut bytes,
                base_digit_bits,
                base_digit_mask,
                base_digits,
                capacity,
            );
        }

        #[cfg(debug_assertions)]
        {
            // Check that no reallocation occurred
            debug_assert_eq!(bytes.capacity(), initial_capacity);
            // Check that len is equal to requested capacity
            debug_assert_eq!(bytes.len(), capacity);
        }

        String::from_utf8(bytes).unwrap()
    }

    fn process_digits_base_pow2_aligned(
        &self,
        bytes: &mut Vec<u8>,
        base_digit_bits: u32,
        base_digit_mask: Digit,
        base_digits: &[u8; 36],
        start_from_msd: bool,
    ) {
        let batches_per_digit = Digit::BITS / base_digit_bits;

        match start_from_msd {
            true => {
                // This avoids the need to reverse `bytes` at the end and
                // benchmarks show that this is also a little more efficient.
                if self.is_negative() {
                    bytes.push(b'-');
                }

                /* Handle most significant digit specially */
                let msd_idx = self.size() - 1;
                let msd = self.vec[msd_idx];
                let msd_bits = Digit::BITS - msd.leading_zeros();
                let msd_bits_mod_base_bits = msd_bits % base_digit_bits;

                // Partial chunk
                if msd_bits_mod_base_bits != 0 {
                    let shift = base_digit_bits - msd_bits_mod_base_bits;
                    let value = (msd >> (msd_bits - msd_bits_mod_base_bits))
                        << shift
                        >> shift;
                    bytes.push(base_digits[value as usize]);
                }

                // Full chunks
                let mut shift = msd_bits - msd_bits_mod_base_bits;
                debug_assert!(shift % base_digit_bits == 0);
                while shift != 0 {
                    shift -= base_digit_bits;
                    bytes.push(
                        base_digits
                            [((msd >> shift) & base_digit_mask) as usize],
                    );
                }

                /* Handle remaining digits (all full chunks) */
                let first_shift = (batches_per_digit - 1) * base_digit_bits;
                for &digit in self.vec[..msd_idx].iter().rev() {
                    bytes.push(
                        base_digits[((digit >> first_shift) & base_digit_mask)
                            as usize],
                    );

                    let mut shift = first_shift;
                    debug_assert!(shift % base_digit_bits == 0);
                    while shift != 0 {
                        shift -= base_digit_bits;
                        bytes.push(
                            base_digits
                                [((digit >> shift) & base_digit_mask) as usize],
                        );
                    }
                }
            }
            false => {
                let mut j = 0;
                let last_idx = self.size() - 1;
                while j < last_idx {
                    let mut digit = self.vec[j];
                    for _ in 0..batches_per_digit {
                        bytes.push(
                            base_digits[(digit & base_digit_mask) as usize],
                        );
                        digit >>= base_digit_bits;
                    }
                    j += 1;
                }

                // Handle last digit specially to avoid pushing leading zeros
                let mut digit = self.vec[last_idx];
                while digit != 0 {
                    bytes.push(base_digits[(digit & base_digit_mask) as usize]);
                    digit >>= base_digit_bits;
                }

                if self.is_negative() {
                    bytes.push(b'-');
                }

                bytes.reverse();
            }
        }
    }

    fn process_digits_base_pow2_generic(
        &self,
        bytes: &mut Vec<u8>,
        base_digit_bits: u32,
        base_digit_mask: Digit,
        base_digits: &[u8; 36],
        num_bytes: usize,
    ) {
        // TODO: vec![0; capacity] might be better rather than allocating
        // capacity, then resizing, like we are doing now.
        bytes.resize(num_bytes, 0);

        if self.is_negative() {
            bytes[0] = b'-';
        }

        /* Process base_digit_bits batches */
        let mut output_idx = num_bytes - 1;
        let mut j = 0;
        let mut batch_stop_idx = 0;
        let last_idx = self.size() - 1;
        while j < last_idx {
            let mut cur = self.vec[j] >> batch_stop_idx;
            batch_stop_idx += base_digit_bits;

            if Digit::BITS <= batch_stop_idx {
                // For < case, batch crosses digit boundaries (takes bits from
                // both the current and next digit).
                j += 1;
                batch_stop_idx -= Digit::BITS;

                // Technically, this is not needed for the = case, but we do
                // need to update counters, as above.
                cur |= self.vec[j] << (base_digit_bits - batch_stop_idx);
            }

            bytes[output_idx] = base_digits[(cur & base_digit_mask) as usize];
            output_idx = output_idx.wrapping_sub(1);
        }

        // Handle last digit
        let last_digit = self.vec[last_idx];
        let msb = Digit::BITS - last_digit.leading_zeros();
        while batch_stop_idx < msb {
            let cur = (last_digit >> batch_stop_idx) & base_digit_mask;
            bytes[output_idx] = base_digits[cur as usize];
            output_idx = output_idx.wrapping_sub(1);
            batch_stop_idx += base_digit_bits;
        }

        debug_assert_eq!(
            output_idx,
            if self.is_negative() { 0 } else { usize::MAX }
        );
    }

    pub(crate) fn to_string_base_(
        &self,
        base: Base,
        lowercase: bool,
    ) -> String {
        let base: usize = base.value() as usize;
        assert!((2..=36).contains(&base));

        let base_digits = if lowercase {
            BASE_DIGITS_LOWER_BYTES
        } else {
            BASE_DIGITS_UPPER_BYTES
        };

        if self.size() == 0 {
            return "0".into();
        }

        /* Allocate memory for the result. This will be exactly the number of
        bytes needed or higher by one. */
        let mut bytes = Vec::new();
        let capacity: usize = if base.is_power_of_two() {
            // Exact number of bytes needed.
            self.size_base_ref(base as u32)
        } else {
            // Exact number of bytes needed or one more.
            Self::size_base_with_size_bits_maybe_over_by_one(
                base as u32,
                self.size_bits(),
            )
        }
        .try_into()
        .unwrap_or(usize::MAX)
        .saturating_add(usize::from(self.is_negative()));
        bytes.reserve_exact(capacity);

        #[cfg(debug_assertions)]
        let initial_capacity = bytes.capacity();

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

                bytes.push(base_digits[current_digit as usize]);
            }
        }

        if self.is_negative() {
            bytes.push(b'-');
        }

        #[cfg(debug_assertions)]
        {
            // Check that no reallocation occurred
            debug_assert_eq!(bytes.capacity(), initial_capacity);
            // Check that the requested capacity was exact or higher by one
            debug_assert!(
                bytes.len() == capacity || bytes.len() == capacity - 1,
                "Capacity estimate {} should be exact or higher by one than \
                 the true value {}",
                capacity,
                bytes.len()
            );
        }

        bytes.reverse();
        String::from_utf8(bytes).unwrap()
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
    #[inline]
    pub fn to_string_base(&self, base: Base) -> String {
        let lowercase = true;
        if base.value().is_power_of_two() {
            self.to_string_base_pow2(base, lowercase)
        } else {
            self.to_string_base_(base, lowercase)
        }
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
    #[inline]
    pub fn to_string_radix(&self, radix: u32) -> String {
        let base: Base = match radix.try_into() {
            Err(_) => panic!("`radix` is not an integer in [2, 36]"),
            Ok(b) => b,
        };
        self.to_string_base(base)
    }
}

/* TODO: clean up */
#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::util::test::{get_uniform_die, BASE10};
    // use crate::{QDigit, SQDigit};

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
        // assert_eq!(
        //     Arbi::from(QDigit::MAX).to_string_base(b),
        //     (QDigit::MAX).to_string_base(b)
        // );
        // assert_eq!(
        //     Arbi::from(SQDigit::MIN).to_string_base(b),
        //     (SQDigit::MIN).to_string_base(b)
        // );
        // assert_eq!(
        //     Arbi::from(SQDigit::MAX).to_string_base(b),
        //     (SQDigit::MAX).to_string_base(b)
        // );

        let (mut rng, _) = get_seedable_rng();
        // let udist = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        let udist_digit = get_uniform_die(Digit::MIN, Digit::MAX);

        let mn = i16::MIN / 8;
        let mx = i16::MAX / 8;
        for i in mn..mx {
            // let r: SQDigit = udist.sample(&mut rng);
            let r_digit: Digit = udist_digit.sample(&mut rng);
            // assert_eq!(Arbi::from(r).to_string_base(b), r.to_string_base(b));
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

    fn create_test_number(bits: usize) -> Arbi {
        let mut num = Arbi::from(1);
        for _ in 0..bits - 1 {
            num <<= 1;
            num += 1;
        }
        num
    }

    #[test]
    fn pow2_base_tests() {
        use crate::util::test::random_arbi;

        let pow2_bases = [2, 4, 8, 16, 32];
        let bit_sizes = [
            1, 2, 3, 4, 30, 31, 32, 33, 34, 62, 63, 64, 65, 66, 1024, 4096,
        ];

        for &bits in &bit_sizes {
            for _ in 0..1000 {
                let random_num = random_arbi(bits);
                let neg_random = -random_num.clone();

                for &base in &pow2_bases {
                    let base = Base::try_from(base).unwrap();

                    // Positive
                    let pow2_result =
                        random_num.to_string_base_pow2(base, true);
                    let general_result = random_num.to_string_base_(base, true);
                    assert_eq!(pow2_result, general_result,);

                    // Negative
                    let neg_pow2_result =
                        neg_random.to_string_base_pow2(base, true);
                    let neg_general_result =
                        neg_random.to_string_base_(base, true);
                    assert_eq!(neg_pow2_result, neg_general_result,);
                }
            }

            let num = create_test_number(bits);
            let neg_num = -num.clone();
            for &base in &pow2_bases {
                let base = Base::try_from(base).unwrap();

                // Positive
                let pow2_result = num.to_string_base_pow2(base, true);
                let general_result = num.to_string_base_(base, true);
                assert_eq!(pow2_result, general_result,);

                // Negative
                let neg_pow2_result = neg_num.to_string_base_pow2(base, true);
                let neg_general_result = neg_num.to_string_base_(base, true);
                assert_eq!(neg_pow2_result, neg_general_result,);
            }
        }

        let cases = [
            Arbi::zero(),
            Arbi::from(1),
            Arbi::from(-1),
            create_test_number(1),
            create_test_number(63),
            create_test_number(64),
            create_test_number(65),
            create_test_number(127),
            create_test_number(128),
            create_test_number(129),
        ];

        for num in cases.iter() {
            for &base in &pow2_bases {
                let base = Base::try_from(base).unwrap();
                let pow2_result = num.to_string_base_pow2(base, true);
                let general_result = num.to_string_base_(base, true);
                assert_eq!(pow2_result, general_result,);
            }
        }
    }
}
