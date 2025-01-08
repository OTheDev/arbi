/*
Copyright 2024 Owain Davies
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
        } else {
            let mut digit = self.vec[digit_idx];
            if self.is_negative() {
                digit = digit.wrapping_neg();
                if self.vec[..digit_idx].iter().any(|&dig| dig != 0) {
                    digit = digit.wrapping_sub(1);
                }
            }
            ((digit >> (i % Digit::BITS as BitCount)) & 1) != 0
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
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
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

    #[test]
    fn test_clear_set_invert_bit_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(0, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let mut r = die_digit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.size_bits() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as Digit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as Digit) << (i as BitCount);
            assert_eq!(a, r);
            a.invert_bit(i);
            r ^= (1 as Digit) << (i as BitCount);
            assert_eq!(a, r);

            let mut r = die_ddigit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.size_bits() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as DDigit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as DDigit) << (i as BitCount);
            assert_eq!(a, r);
            a.invert_bit(i);
            r ^= (1 as DDigit) << (i as BitCount);
            assert_eq!(a, r);

            let mut r = die_qdigit.sample(&mut rng);
            let mut a = Arbi::from(r);
            let die = get_uniform_die(1, a.size_bits() - 1);
            let i = die.sample(&mut rng);
            a.clear_bit(i);
            r &= !((1 as QDigit) << i);
            assert_eq!(a, r);
            a.set_bit(i);
            r |= (1 as QDigit) << (i as BitCount);
            assert_eq!(a, r);
            a.invert_bit(i);
            r ^= (1 as QDigit) << (i as BitCount);
            assert_eq!(a, r);
        }
    }

    #[test]
    fn test_clear_bit() {
        assert_eq!(Arbi::zero().set_bit(0), 1);
        assert_eq!(Arbi::from(10).set_bit(2), 14);

        for i in 0..=53 {
            let mut a = Arbi::from(2.0_f64.powi(i as i32));
            a.clear_bit(i as BitCount);
            assert_eq!(a, 0);
        }
    }

    #[test]
    fn test_set_and_test_bit() {
        assert_eq!(Arbi::zero().set_bit(0), 1);
        assert_eq!(Arbi::from(10).set_bit(2), 14);

        for i in 0..=53 {
            let mut a = Arbi::zero();
            a.set_bit(i as BitCount);
            assert_eq!(a, (2.0_f64.powi(i as i32)));
            assert!(a.test_bit(i as BitCount));
        }
    }

    #[test]
    fn test_test_bit() {
        // Zero
        let x = Arbi::zero();
        assert_eq!(x.test_bit(0), false);
        assert_eq!(x.test_bit(42040), false);

        // One
        let x = Arbi::one();
        assert_eq!(x.test_bit(0), true);
        for i in 1..256 {
            assert_eq!(x.test_bit(i), false);
        }

        // 1010 (MSB is the 1)
        let x = Arbi::from(10);
        assert_eq!(x.test_bit(0), false);
        assert_eq!(x.test_bit(1), true);
        assert_eq!(x.test_bit(2), false);
        assert_eq!(x.test_bit(3), true);
        for i in 4..256 {
            assert_eq!(x.test_bit(i), false);
        }

        // Powers of Two
        let mut one = Arbi::one();
        one <<= 1_usize;
        for i in 1..65000 {
            assert_eq!(one.test_bit(i - 1), false);
            assert_eq!(one.test_bit(i), true, "Failure at i = {}", i);
            assert_eq!(one.test_bit(i + 1), false);
            one <<= 1_usize;
        }
    }

    #[test]
    fn test_test_bit_negative_single_digit() {
        // Negative one
        let x = Arbi::neg_one();
        for i in 0..256 {
            assert_eq!(x.test_bit(i), true);
        }

        // 110
        let x = Arbi::from(-2);
        assert_eq!(x.test_bit(0), false);
        assert_eq!(x.test_bit(1), true);
        for i in 2..256 {
            assert_eq!(x.test_bit(i), true);
        }

        // 101
        let x = Arbi::from(-3);
        assert_eq!(x.test_bit(0), true);
        assert_eq!(x.test_bit(1), false);
        for i in 2..256 {
            assert_eq!(x.test_bit(i), true);
        }

        // 1011
        let x = Arbi::from(-5);
        assert_eq!(x.test_bit(0), true);
        assert_eq!(x.test_bit(1), true);
        assert_eq!(x.test_bit(2), false);
        for i in 3..256 {
            assert_eq!(x.test_bit(i), true);
        }
    }

    #[test]
    fn test_test_bit_negative_multiple_digits() {
        // 10110010000011110000011100100110110000101111000100110001110110111
        let v = -11232524694493961289_i128;
        let x = Arbi::from(v);
        for i in 0u32..128u32 {
            assert_eq!(
                x.test_bit(i as BitCount),
                test_i128_bit(v, i),
                "Failed for value {} at index {}",
                v,
                i
            );
        }
    }

    macro_rules! test_bit_value {
        ($rng:expr, $die:expr) => {
            let v = $die.sample(&mut $rng) as i128;
            let x = Arbi::from(v);
            for i in 0..i128::BITS {
                assert_eq!(
                    x.test_bit(i as BitCount),
                    test_i128_bit(v, i),
                    "Failed for value {} at index {}",
                    v,
                    i
                );
            }
        };
    }

    #[test]
    fn test_test_bit_negative_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        for _ in 0..i16::MAX {
            test_bit_value!(rng, die_sdigit);
            test_bit_value!(rng, die_sddigit);
            test_bit_value!(rng, die_sqdigit);
        }
    }

    macro_rules! test_arbi_variants_test {
        ($die_digit:expr, $rng:expr, $( $vec:expr ),* ) => {
            $(
                let arbi = Arbi {
                    vec: $vec,
                    neg: true,
                };
                let v = match arbi.checked_to_i128() {
                    Some(v) => v,
                    None => continue,
                };
                for i in 0..(i128::BITS - 1) {
                    let x = Arbi::from(v);
                    assert_eq!(
                        x.test_bit(i as BitCount),
                        test_i128_bit(v, i),
                        "Failed for value {} at index {}",
                        v,
                        i
                    );
                }
            )*
        };
    }

    #[test]
    fn test_test_bit_branch() {
        let arbi = Arbi {
            vec: vec![0, 0, 583274041, 681312275],
            neg: true,
        };
        let val = arbi.checked_to_i128().unwrap();
        assert_eq!(val, -53979119657422662756390826147269574656_i128);
        let idx = 32;
        assert_eq!(arbi.test_bit(idx), test_i128_bit(val, idx as u32));

        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        for _ in 0..1000 {
            test_arbi_variants_test!(
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

    macro_rules! test_set_bit_value {
        ($rng:expr, $die:expr) => {
            let v = $die.sample(&mut $rng) as i128;
            for i in 0..(i128::BITS - 1) {
                let mut x = Arbi::from(v);
                x.set_bit(i as BitCount);
                assert_eq!(
                    x,
                    set_i128_bit(v, i),
                    "Failed for value {} at index {}",
                    v,
                    i
                );
            }
        };
    }

    #[test]
    fn test_set_bit_negative_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        for _ in 0..i16::MAX {
            test_set_bit_value!(rng, die_sdigit);
            test_set_bit_value!(rng, die_sddigit);
            test_set_bit_value!(rng, die_sqdigit);
        }
    }

    #[test]
    fn test_set_bit_ordering_greater_branch() {
        let val = -4866991881022244489_i128;
        let mut arbi = Arbi::from(val);
        let idx = 32;
        assert_eq!(arbi.set_bit(idx), set_i128_bit(val, idx as u32));
    }

    #[test]
    fn test_set_bit_ordering_equal_branch() {
        let val = -1407405570_i128;
        let mut arbi = Arbi::from(val);
        let idx = 0;
        assert_eq!(arbi.set_bit(idx), set_i128_bit(val, idx as u32));
    }

    macro_rules! test_arbi_variants {
        ($die_digit:expr, $rng:expr, $( $vec:expr ),* ) => {
            $(
                let arbi = Arbi {
                    vec: $vec,
                    neg: true,
                };
                let v = match arbi.checked_to_i128() {
                    Some(v) => v,
                    None => continue,
                };
                for i in 0..(i128::BITS - 1) {
                    let mut x = Arbi::from(v);
                    x.set_bit(i as BitCount);
                    assert_eq!(
                        x,
                        set_i128_bit(v, i),
                        "Failed for value {} at index {}",
                        v,
                        i
                    );
                }
            )*
        };
    }

    #[test]
    fn test_set_bit_ordering_less_branch() {
        let mut arbi = Arbi {
            vec: vec![0, 0, 583274041, 681312275],
            neg: true,
        };
        let val = arbi.checked_to_i128().unwrap();
        assert_eq!(val, -53979119657422662756390826147269574656_i128);
        let idx = 32;
        assert_eq!(arbi.set_bit(idx), set_i128_bit(val, idx as u32));

        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        for _ in 0..1000 {
            test_arbi_variants!(
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

    macro_rules! test_clear_bit_value {
        ($rng:expr, $die:expr) => {
            let v = $die.sample(&mut $rng) as i128;
            for i in 0..(i128::BITS - 1) {
                let mut x = Arbi::from(v);
                x.clear_bit(i as BitCount);
                assert_eq!(
                    x,
                    clear_i128_bit(v, i),
                    "Failed for value {} at index {}",
                    v,
                    i
                );
            }
        };
    }

    #[test]
    fn test_clear_bit_negative_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        for _ in 0..i16::MAX {
            test_clear_bit_value!(rng, die_sdigit);
            test_clear_bit_value!(rng, die_sddigit);
            test_clear_bit_value!(rng, die_sqdigit);
        }
    }

    macro_rules! test_arbi_variants_clear {
        ($die_digit:expr, $rng:expr, $( $vec:expr ),* ) => {
            $(
                let arbi = Arbi {
                    vec: $vec,
                    neg: true,
                };
                let v = match arbi.checked_to_i128() {
                    Some(v) => v,
                    None => continue,
                };
                for i in 0..(i128::BITS - 1) {
                    let mut x = Arbi::from(v);
                    x.clear_bit(i as BitCount);
                    assert_eq!(
                        x,
                        clear_i128_bit(v, i),
                        "Failed for value {} at index {}",
                        v,
                        i
                    );
                }
            )*
        };
    }

    #[test]
    fn test_clear_bit_branch() {
        let mut arbi = Arbi {
            vec: vec![0, 0, 583274041, 681312275],
            neg: true,
        };
        let val = arbi.checked_to_i128().unwrap();
        assert_eq!(val, -53979119657422662756390826147269574656_i128);
        let idx = 32;
        assert_eq!(arbi.clear_bit(idx), clear_i128_bit(val, idx as u32));

        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        for _ in 0..1000 {
            test_arbi_variants_clear!(
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

    #[test]
    fn test_clear_bit_b() {
        // l
        let val = -53979119657422662756390826147269574656_i128;
        let mut arbi = Arbi::from(val);
        let idx = 32;
        assert_eq!(arbi.clear_bit(idx), clear_i128_bit(val, idx as u32));

        // e
        let val = -2123323316_i128;
        let mut arbi = Arbi::from(val);
        let idx = 0;
        assert_eq!(arbi.clear_bit(idx), clear_i128_bit(val, idx as u32));

        // g
        let val = -4271208378563570_i128;
        let mut arbi = Arbi::from(val);
        let idx = 0;
        assert_eq!(arbi.clear_bit(idx), clear_i128_bit(val, idx as u32));
    }

    macro_rules! test_invert_bit_value {
        ($rng:expr, $die:expr) => {
            let v = $die.sample(&mut $rng) as i128;
            for i in 0..(i128::BITS - 1) {
                let mut x = Arbi::from(v);
                x.invert_bit(i as BitCount);
                assert_eq!(
                    x,
                    invert_i128_bit(v, i),
                    "Failed for value {} at index {}",
                    v,
                    i
                );
            }
        };
    }

    #[test]
    fn test_invert_bit_negative_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        for _ in 0..i16::MAX {
            test_invert_bit_value!(rng, die_sdigit);
            test_invert_bit_value!(rng, die_sddigit);
            test_invert_bit_value!(rng, die_sqdigit);
        }
    }

    macro_rules! test_arbi_variants_invert {
        ($die_digit:expr, $rng:expr, $( $vec:expr ),* ) => {
            $(
                let arbi = Arbi {
                    vec: $vec,
                    neg: true,
                };
                let v = match arbi.checked_to_i128() {
                    Some(v) => v,
                    None => continue,
                };
                for i in 0..(i128::BITS - 1) {
                    let mut x = Arbi::from(v);
                    x.invert_bit(i as BitCount);
                    assert_eq!(
                        x,
                        invert_i128_bit(v, i),
                        "Failed for value {} at index {}",
                        v,
                        i
                    );
                }
            )*
        };
    }

    #[test]
    fn test_invert_bit_branch() {
        let mut arbi = Arbi {
            vec: vec![0, 0, 583274041, 681312275],
            neg: true,
        };
        let val = arbi.checked_to_i128().unwrap();
        assert_eq!(arbi, val);
        let idx = 32;
        arbi.invert_bit(idx);
        assert_eq!(arbi, invert_i128_bit(val, idx as u32));

        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        for _ in 0..1000 {
            test_arbi_variants_invert!(
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
