/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Functions to test, set, clear, and toggle a bit at a specified index.
//!
//! Operates on the two's complement representation of an integer, with sign
//! extension.

// Consider magnitude A:
//
//           leftmost 0 is the (imaginary) sign bit
//           |-------------------
//                   1 is the first nonzero bit (f)
//                   |-----------
//                           rightmost bit is bit with index 0
//                           |
//      A = (0 bits  1 0 --- 0)_2
//
// -A is represented in two's complement (obtained by inverting bits in A and
// adding 1) as:
//
//           leftmost 1 is the (imaginary) sign bit
//           |----------------
//                   1 is the first nonzero bit (f)
//                   |--------
//                           rightmost bit is bit with index 0
//                           |
//     -A = (1 ~bits 1 0 --- 0)_2
//
// Suppose we need to set (clear) bit j in -A, but we only store (A, sign). What
// should the the bit representation of the new magnitude A' be and what's an
// algorithm that will modify A to become A'?
//
// -----------------------------------------------------------------------------
// Case 1: j < f
// -----------------------------------------------------------------------------
//  SET
//      (-A)':
//                           position j (around are all 0s)
//                           |---------
//          (1 ~bits 1 0 --- 1 --- 0)_2
//      ~(-A)':
//                           position j (around are all 1s)
//                           |---------
//          (0 bits  0 1 --- 0 --- 1)_2
//      A' = ~(-A)' + 1:
//                   position f (becomes 0)
//                   |-----------------
//                           position j (1s to left, 0s to right)
//                           |---------
//          (0 bits  0 1 --- 1 --- 0)_2
//      A:
//                   position f
//                   |-----------------
//                           position j
//                           |---------
//          (0 bits  1 0 --- 0 --- 0)_2
//
//      To get A' from A:
//          (1) Clear bit f
//          (2) Set bits [f - 1, j].
//
//  CLEAR
//      A' = A  [It's already cleared, no change needed]
//
//  INVERT
//      Bit j is 0 ==> same as setting bit j.
//
// -----------------------------------------------------------------------------
// Case 2: j = f
// -----------------------------------------------------------------------------
//  SET
//      A' = A  [It's already set, no change needed]
//
//  CLEAR
//      -A:
//                   position of f (first nonzero bit)
//                   |-----------
//          (1 ~bits 1 0 --- 0)_2
//      (-A)':
//          (1 ~bits 0 0 --- 0)_2   [Clear bit at position f]
//      ~(-A)':
//          (0 bits  1 1 --- 1)_2
//      A' = ~(-A)' + 1:
//          ([other] 0 0 --- 0)_2   [where other is bits + 1]
//
//      To get A' from A:
//          (1) Clear bit f
//          (2) Add 1 to bit field with indices > f: (f, inf).
//
//  INVERT
//      Bit j is 1 ==> same as clearing bit j.
//
// -----------------------------------------------------------------------------
// Case 3: j > f
// -----------------------------------------------------------------------------
//  In -A, the relevant part is "~bits" which corresponds to "bits" in the
//  magnitude.
//
//  SET
//      Setting a bit in "~bits" is equivalent to clearing it in "bits". Thus
//
//      A' = A & ~(1 << j)
//
//  CLEAR
//      Clearing a bit in "~bits" is equivalent to setting it in "bits". Thus
//
//      A' = A | (1 << j)
//
// INVERT
//      XOR. TODO.

use crate::{Arbi, BitCount, Digit};
use core::cmp::Ordering;

impl Arbi {
    fn first_nonzero_bit(&self) -> (usize, usize, BitCount) {
        assert!(!self.is_zero());
        let mut f_digit_idx = 0;
        let mut f_bit_idx = 0;
        for (idx, &digit) in self.vec.iter().enumerate() {
            if digit != 0 {
                f_digit_idx = idx;
                f_bit_idx = digit.trailing_zeros() as BitCount;
                break;
            }
        }
        let f = (f_digit_idx as BitCount) * Digit::BITS as BitCount + f_bit_idx;
        (f_digit_idx, f_bit_idx as usize, f)
    }

    /// Test bit `i` of the two's complement representation (with sign
    /// extension) of this integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// // 11000000111001 (bit indices [0, 13])
    /// let a = Arbi::from(12345);
    /// assert_eq!(a.test_bit(0), true);
    /// assert_eq!(a.test_bit(1), false);
    /// assert_eq!(a.test_bit(5), true);
    /// assert_eq!(a.test_bit(13), true);
    /// // 14 is not in [0, size_bits()). Bits outside of this range (for
    /// // nonnegative integers) are treated as false.
    /// assert_eq!(a.test_bit(14), false);
    /// ```
    pub fn test_bit(&self, i: BitCount) -> bool {
        let digit_idx = (i / Digit::BITS as BitCount) as usize;
        if self.size() <= digit_idx {
            self.is_negative()
        } else if !self.is_negative() {
            ((self.vec[digit_idx] >> (i % Digit::BITS as BitCount)) & 1) != 0
        } else {
            let (_, _, f) = self.first_nonzero_bit();
            match i.cmp(&f) {
                Ordering::Less => false,
                Ordering::Equal => true,
                Ordering::Greater => {
                    ((self.vec[digit_idx] >> (i % Digit::BITS as BitCount)) & 1)
                        == 0
                }
            }
        }
    }

    /// Set bit `i` of the two's complement representation (with sign extension)
    /// of this integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// // 11000000111001
    /// let mut a = Arbi::from(12345);
    /// a.set_bit(1);
    /// // 11000000111011
    /// assert_eq!(a, 12347);
    /// a.set_bit(14);
    /// // 111000000111011
    /// assert_eq!(a, 28731);
    /// ```
    pub fn set_bit(&mut self, i: BitCount) -> &mut Self {
        let digit_idx: usize = (i / Digit::BITS as BitCount)
            .try_into()
            .unwrap_or(usize::MAX);
        #[allow(clippy::useless_conversion)]
        let m = Digit::from(1u32) << (i % Digit::BITS as BitCount);
        if !self.is_negative() {
            if digit_idx >= self.size() {
                self.vec.resize(digit_idx.saturating_add(1), 0);
            }
            self.vec[digit_idx] |= m;
        } else {
            if digit_idx >= self.size() {
                // With sign extension, these bits are already set
                return self;
            }
            let (f_digit_idx, f_bit_idx, f) = self.first_nonzero_bit();
            match i.cmp(&f) {
                Ordering::Less => {
                    #[allow(clippy::useless_conversion)]
                    let f_mask = Digit::from(1u32) << f_bit_idx;
                    // Clear bit f
                    self.vec[f_digit_idx] &= !f_mask;
                    // Set bits [f-1, j]
                    if f_digit_idx == digit_idx {
                        self.vec[digit_idx] |= (f_mask - 1) & !(m - 1);
                    } else {
                        self.vec[f_digit_idx] |= f_mask - 1;
                        for idx in (digit_idx + 1)..f_digit_idx {
                            self.vec[idx] = Digit::MAX;
                        }
                        self.vec[digit_idx] |= !(m - 1);
                    }
                }
                Ordering::Equal => (),
                Ordering::Greater => {
                    self.vec[digit_idx] &= !m;
                }
            }
        }
        self.trim();
        self
    }

    /// Clear bit `i` of the two's complement representation (with sign
    /// extension) of this integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// // 11000000111001
    /// let mut a = Arbi::from(12345);
    /// a.clear_bit(0);
    /// // 11000000111000
    /// assert_eq!(a, 12344);
    /// a.clear_bit(13);
    /// // 1000000111000
    /// assert_eq!(a, 4152);
    /// a.clear_bit(13);
    /// assert_eq!(a, 4152);
    /// ```
    #[allow(clippy::useless_conversion)]
    pub fn clear_bit(&mut self, i: BitCount) -> &mut Self {
        let digit_idx: usize = (i / Digit::BITS as BitCount)
            .try_into()
            .unwrap_or(usize::MAX);
        let m = Digit::from(1u32) << (i % Digit::BITS as BitCount);
        if !self.is_negative() {
            if digit_idx < self.size() {
                // Clear bit
                self.vec[digit_idx] &= !m;
            } else {
                /* Already clear */
            }
        } else if digit_idx >= self.size() {
            self.vec.resize(digit_idx.saturating_add(1), 0);
            self.vec[digit_idx] = m;
        } else {
            let (f_digit_idx, f_bit_idx, f) = self.first_nonzero_bit();
            match i.cmp(&f) {
                Ordering::Less => { /* Already clear */ }
                Ordering::Equal => {
                    // Clear bit f
                    self.vec[f_digit_idx] &= !(Digit::from(1u32) << f_bit_idx);
                    // For f's digit: add 1 only to bits more significant than f
                    let high_m = !((Digit::from(1u32) << (f_bit_idx + 1)) - 1);
                    let sum = (self.vec[f_digit_idx] & high_m)
                        .wrapping_add(Digit::from(1u32) << (f_bit_idx + 1));
                    let mut carry =
                        (sum & high_m) < (self.vec[f_digit_idx] & high_m);
                    self.vec[f_digit_idx] =
                        (self.vec[f_digit_idx] & !high_m) | (sum & high_m);
                    // Propagate carry if needed
                    if carry {
                        for digit in &mut self.vec[f_digit_idx + 1..] {
                            let (new_digit, overflow) =
                                digit.overflowing_add(1);
                            *digit = new_digit;
                            if !overflow {
                                carry = false;
                                break;
                            }
                        }
                        if carry {
                            self.vec.push(1);
                        }
                    }
                }
                Ordering::Greater => {
                    self.vec[digit_idx] |= m;
                }
            }
        }
        self.trim();
        self
    }

    /* TODO: for the negative case, we can avoid using self.test_bit() */
    /// Toggle bit `i` of the two's complement representation (with sign
    /// extension) of this integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(0xf); // 0b1111
    /// a.invert_bit(0); // 0b1110
    /// assert_eq!(a, 0b1110);
    /// a.invert_bit(4); // 0b11110
    /// assert_eq!(a, 0b11110);
    /// ```
    pub fn invert_bit(&mut self, i: BitCount) -> &mut Self {
        if !self.is_negative() {
            let digit_idx: usize = (i / Digit::BITS as BitCount)
                .try_into()
                .unwrap_or(usize::MAX);
            #[allow(clippy::useless_conversion)]
            let m = Digit::from(1u32) << (i % Digit::BITS as BitCount);
            if digit_idx >= self.size() {
                self.vec.resize(digit_idx.saturating_add(1), 0);
            }
            self.vec[digit_idx] ^= m;
            self.trim();
            self
        } else if self.test_bit(i) {
            self.clear_bit(i)
        } else {
            self.set_bit(i)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{BitCount, DDigit, Digit, QDigit, SDDigit, SDigit, SQDigit};

    fn test_i128_bit(v: i128, i: u32) -> bool {
        assert!(i < 128);
        let m = 1_i128 << i;
        (v & m) != 0
    }

    fn set_i128_bit(mut v: i128, i: u32) -> i128 {
        assert!(i < 128);
        let m = 1_i128 << i;
        v |= m;
        v
    }

    fn clear_i128_bit(mut v: i128, i: u32) -> i128 {
        assert!(i < 128);
        let m = 1_i128 << i;
        v &= !m;
        v
    }

    fn invert_i128_bit(mut v: i128, i: u32) -> i128 {
        assert!(i < 128);
        let m = 1_i128 << i;
        v ^= m;
        v
    }

    #[cfg(test)]
    mod random {
        use super::*;

        macro_rules! test_bit_ops_for_type {
            ($rng:expr, $die:expr) => {
                let v = $die.sample(&mut $rng) as i128;
                for i in 0..(i128::BITS - 1) {
                    // Test
                    let x = Arbi::from(v);
                    assert_eq!(
                        x.test_bit(i as BitCount),
                        test_i128_bit(v, i),
                        "test_bit failed for value {} at index {}",
                        v,
                        i
                    );

                    // Set
                    let mut x = Arbi::from(v);
                    x.set_bit(i as BitCount);
                    assert_eq!(
                        x,
                        set_i128_bit(v, i),
                        "set_bit failed for value {} at index {}",
                        v,
                        i
                    );

                    // Clear
                    let mut x = Arbi::from(v);
                    x.clear_bit(i as BitCount);
                    assert_eq!(
                        x,
                        clear_i128_bit(v, i),
                        "clear_bit failed for value {} at index {}",
                        v,
                        i
                    );

                    // Invert
                    let mut x = Arbi::from(v);
                    x.invert_bit(i as BitCount);
                    assert_eq!(
                        x,
                        invert_i128_bit(v, i),
                        "invert_bit failed for value {} at index {}",
                        v,
                        i
                    );
                }
            };
        }

        #[test]
        fn test_bit_operations_smoke() {
            let (mut rng, _) = get_seedable_rng();
            let die_digit = get_uniform_die(0, Digit::MAX);
            let die_ddigit =
                get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
            let die_qdigit =
                get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);
            let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
            let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
            let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

            for _ in 0..i16::MAX {
                test_bit_ops_for_type!(rng, die_digit);
                test_bit_ops_for_type!(rng, die_ddigit);
                test_bit_ops_for_type!(rng, die_qdigit);
                test_bit_ops_for_type!(rng, die_sdigit);
                test_bit_ops_for_type!(rng, die_sddigit);
                test_bit_ops_for_type!(rng, die_sqdigit);
            }
        }

        macro_rules! test_arbi_trailing_zeros_all_ops {
            ($die_digit:expr, $rng:expr, $($vec:expr),* ) => {
                $(
                    let arbi = Arbi::from_digits($vec, true);
                    let v = match arbi.checked_to_i128() {
                        Some(v) => v,
                        None => continue,
                    };
                    for i in 0..(i128::BITS - 1) {
                        // Test
                        let x = Arbi::from(v);
                        assert_eq!(
                            x.test_bit(i as BitCount),
                            test_i128_bit(v, i),
                            "test_bit failed for value {} at index {}",
                            v,
                            i
                        );

                        // Set
                        let mut x = Arbi::from(v);
                        x.set_bit(i as BitCount);
                        assert_eq!(
                            x,
                            set_i128_bit(v, i),
                            "set_bit failed for value {} at index {}",
                            v,
                            i
                        );

                        // Clear
                        let mut x = Arbi::from(v);
                        x.clear_bit(i as BitCount);
                        assert_eq!(
                            x,
                            clear_i128_bit(v, i),
                            "clear_bit failed for value {} at index {}",
                            v,
                            i
                        );

                        // Invert
                        let mut x = Arbi::from(v);
                        x.invert_bit(i as BitCount);
                        assert_eq!(
                            x,
                            invert_i128_bit(v, i),
                            "invert_bit failed for value {} at index {}",
                            v,
                            i
                        );
                    }
                )*
            };
        }

        #[test]
        fn test_arbi_trailing_zeros() {
            let (mut rng, _) = get_seedable_rng();
            let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
            for _ in 0..1000 {
                test_arbi_trailing_zeros_all_ops!(
                    die_digit,
                    rng,
                    vec![
                        0,
                        die_digit.sample(&mut rng),
                        die_digit.sample(&mut rng),
                        die_digit.sample(&mut rng),
                    ],
                    vec![
                        0,
                        0,
                        die_digit.sample(&mut rng),
                        die_digit.sample(&mut rng),
                    ],
                    vec![0, 0, 0, die_digit.sample(&mut rng)]
                );
            }
        }
    }

    #[cfg(test)]
    mod spec_test_bit {
        use super::*;

        fn check_test_bit(v: i128, i: u32) {
            let a = Arbi::from(v);
            assert_eq!(a.test_bit(i as BitCount), test_i128_bit(v, i));
        }

        #[test]
        fn test_test_bit_size_lte_digit_idx_positive() {
            check_test_bit(2794480102, 32);
            check_test_bit(3213823657745546596, 64);
        }

        #[test]
        fn test_test_bit_size_lte_digit_idx_negative() {
            check_test_bit(-1094350350, 32);
            check_test_bit(-1445413578913102255, 64);
        }

        #[test]
        fn test_test_bit_size_gt_digit_idx_positive() {
            check_test_bit(4142986110, 0);
            check_test_bit(12328930459554309820, 1);
        }

        #[test]
        fn test_test_bit_size_gt_digit_idx_negative_ordering_less() {
            check_test_bit(-8358488063644604456, 0);
        }

        #[test]
        fn test_test_bit_size_gt_digit_idx_negative_ordering_equal() {
            check_test_bit(-278205108, 2);
        }

        #[test]
        fn test_test_bit_size_gt_digit_idx_negative_ordering_greater() {
            check_test_bit(-1630333990, 2);
            check_test_bit(-145885073049663941, 33);
        }
    }

    #[cfg(test)]
    mod spec_set_bit {
        use super::*;

        fn check_set_bit(v: i128, i: u32) {
            let mut a = Arbi::from(v);
            a.set_bit(i as BitCount);
            assert_eq!(a, set_i128_bit(v, i));
        }

        #[test]
        fn test_set_bit_nonnegative_digit_idx_gte_size() {
            check_set_bit(231225232, 32);
            check_set_bit(1117149505875380525, 64);
        }

        #[test]
        fn test_set_bit_nonnegative_digit_idx_lt_size() {
            check_set_bit(3624511275, 0);
            check_set_bit(1731705162, 11);
        }

        #[test]
        fn test_set_bit_negative_digit_idx_gte_size() {
            check_set_bit(-5195882671383705216, 64);
        }

        #[test]
        fn test_set_bit_negative_ordering_less() {
            check_set_bit(-66142783587514876610185198462355676004, 0);
            check_set_bit(-65062158611235322364225102006062153728, 0);
            check_set_bit(-135942508526365600474330669961831251968, 32);
            check_set_bit(-38035140290876007155503263883093606400, 64);
            check_set_bit(-135942508526365600437437181814412148736, 32);
            check_set_bit(-113029729128887551475283106339106062336, 35);
        }

        #[test]
        fn test_set_bit_negative_ordering_greater() {
            check_set_bit(-42118996697395892268090367623661261034, 2);
        }

        #[test]
        fn test_set_bit_negative_ordering_equal() {
            check_set_bit(-2131484967, 0);
            check_set_bit(-79104890842846643010291851066536361984, 33);
        }
    }

    #[cfg(test)]
    mod spec_invert_bit {
        use super::*;

        fn check_invert_bit(v: i128, i: u32) {
            let mut a = Arbi::from(v);
            a.invert_bit(i as BitCount);
            assert_eq!(a, invert_i128_bit(v, i));
        }

        #[test]
        fn test_invert_bit_nonnegative_digit_idx_gte_size() {
            check_invert_bit(3169162174, 35);
            check_invert_bit(5297922818921732749, 64);
        }

        #[test]
        fn test_invert_bit_nonnegative_digit_idx_lt_size() {
            check_invert_bit(3220136555740037207, 0);
            check_invert_bit(9577613604812561155, 35);
        }

        // TODO: for now, negative cases can be covered by the tests for test,
        // set, and clear bit as invert bit is currently implemented in
        // terms of them.
    }

    #[cfg(test)]
    mod spec_clear_bit {
        use super::*;

        fn check_clear_bit(v: i128, i: u32) {
            let mut a = Arbi::from(v);
            a.clear_bit(i as BitCount);
            assert_eq!(a, clear_i128_bit(v, i));
        }

        #[test]
        fn test_clear_bit_nonnegative_digit_idx_lt_size() {
            check_clear_bit(8165514632630324252, 35);
            check_clear_bit(4207883224, 0);
            check_clear_bit(1983355790, 1);
        }

        #[test]
        fn test_clear_bit_nonnegative_digit_idx_gte_size() {
            check_clear_bit(4227601892, 32);
            check_clear_bit(1656726456, 33);
        }

        #[test]
        fn test_clear_bit_negative_digit_idx_gte_size() {
            check_clear_bit(-1312369833, 33);
            check_clear_bit(-2064297443, 32);
            check_clear_bit(-1131893546, 66);
            check_clear_bit(-8608514187077909673, 66);
        }

        #[test]
        fn test_clear_bit_negative_ordering_less() {
            check_clear_bit(-18965961268936630417225958052012752896, 66);
            check_clear_bit(-121952855773553855296845216926711967744, 11);
        }

        #[test]
        fn test_clear_bit_negative_ordering_greater() {
            check_clear_bit(-1264686768109554377, 11);
            check_clear_bit(-5329284535033871352930409852495790005, 34);
        }

        #[test]
        fn test_clear_bit_negative_ordering_equal() {
            // No carry propagation
            check_clear_bit(-143140054817892714756379615631696199680, 64);
            check_clear_bit(-42682086721719978017573039099164491776, 32);
            check_clear_bit(-7101851680573794725778516826707998950, 1);
            check_clear_bit(-0b11110000000000000000000000000000000000000, 37);

            // TODO: Generally speaking, the randomized testing above touches
            // all code branches. More specific randomized testing for this
            // branch should probably be added, as these had to be specially
            // contrived.
            // With carry propagation (twice)
            check_clear_bit(-0b11111111111111111111111111111111, 0);
            check_clear_bit(-0b11111111111111111111111111111110, 1);
            check_clear_bit(-0b11111111111111111111111111111100, 2);
            check_clear_bit(-0b11111111111111111111111111111000, 3);
            check_clear_bit(-0b11111111111111111111111111110000, 4);
            check_clear_bit(-0b11111111111111111111111111100000, 5);

            // With carry propagation (once)
            check_clear_bit(-0b111111111111111111111111111111111111111111111111111111111111111111111110, 1);
            check_clear_bit(-0b111111111111111111111111111111111111111111111111111111111111111111111100, 2);
            check_clear_bit(-0b111111111111111111111111111111111111111111111111111111111111111111111000, 3);
            check_clear_bit(-0b111111111111111111111111111111111111111111111111111111111111111111110000, 4);
            check_clear_bit(-0b111111111111111111111111111111111111111111111111111111111111111111100000, 5);
            check_clear_bit(-0b111111111111111110000000000000000000000000000000000000000000000000000000, 55);
            check_clear_bit(-0b111111111111111100000000000000000000000000000000000000000000000000000000, 56);
        }
    }
}
