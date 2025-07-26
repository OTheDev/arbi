/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::macros::for_all_ints;
use crate::{Arbi, BitCount, Digit};
use core::ops::{Shr, ShrAssign};

impl Arbi {
    pub(crate) fn dslice_rshift(digits: &mut [Digit], bits: u32) -> Digit {
        debug_assert!(!digits.is_empty());
        debug_assert!((1..Digit::BITS).contains(&bits));

        let com_bits = Digit::BITS - bits;

        let out = digits[0] << com_bits;
        let mut shifted = digits[0] >> bits;
        for i in 1..digits.len() {
            digits[i - 1] = shifted | (digits[i] << com_bits);
            shifted = digits[i] >> bits;
        }
        digits[digits.len() - 1] = shifted;

        out
    }

    pub(crate) fn dslice_trimmed_size(digits: &[Digit], size: usize) -> usize {
        digits[..size]
            .iter()
            .rposition(|&x| x != 0)
            .map_or(0, |pos| pos + 1)
    }

    pub(crate) fn arithmetic_rshift(&mut self, bits: BitCount) {
        if self.is_zero() {
            return;
        }

        let is_neg = self.is_negative();

        let dig_shift = (bits / Digit::BITS as BitCount)
            .try_into()
            .unwrap_or(usize::MAX); // `new_size` will be 0 if dig_shift is MAX
        let bit_shift = (bits % Digit::BITS as BitCount) as u32;

        let mut new_size = self.size().saturating_sub(dig_shift);
        if new_size == 0 {
            if is_neg {
                self.make_one(true); // a
            } else {
                self.make_zero(); // b
            }
            return;
        }

        let correction_needed = if is_neg {
            let mask = ((1 as Digit) << bit_shift) - 1;
            (self.vec[dig_shift] & mask) != 0
                || (Self::dslice_trimmed_size(
                    &self.vec[..dig_shift],
                    dig_shift,
                ) != 0)
        } else {
            false
        };

        if dig_shift > 0 {
            self.vec.copy_within(dig_shift.., 0);
        }

        if bit_shift > 0 {
            Self::dslice_rshift(&mut self.vec[..new_size], bit_shift);
            if self.vec[new_size - 1] == 0 {
                new_size -= 1;
            }
        }

        self.vec.truncate(new_size);

        if correction_needed {
            // Add 1 to magnitude
            let mut carry: Digit = 1;
            for digit in self.vec.iter_mut() {
                *digit = digit.wrapping_add(carry);
                carry = Digit::from(*digit == 0);
                if carry == 0 {
                    break;
                }
            }
            if carry > 0 {
                self.vec.push(carry);
            }
        }

        self.neg = is_neg;
        self.trim();
    }
}

/* !impl_shr_integral */
macro_rules! impl_shr_integral {
    ($($bitcount:ty),*) => {
        $(

/// Return an integer representing this integer right-shifted `rhs` bit
/// positions.
///
/// This is an arithmetic right shift with sign extension.
///
/// Mathematically, the value of the resulting integer is \\(
/// \frac{x}{2^{\text{shift}}} \\), rounded down:
/// \\[
///     \left\lfloor \frac{x}{2^{\text{shift}}} \right\rfloor
/// \\]
/// where \\( x \\) is the big integer.
///
/// The right-hand-side (RHS) of a right shift operation can be a nonnegative
/// value of any primitive integer type.
///
/// # Panics
/// Panics if `rhs` is negative.
///
/// # Note
/// When right-shifting a reference to an `Arbi` (`&Arbi`), the operation
/// involves cloning the `Arbi` integer, which incurs memory allocation. To
/// avoid these allocations, prefer using the in-place right-shift operator
/// `>>=` on a mutable reference (`&mut Arbi`), or the move-based right-shift
/// operator `>>` on an `Arbi` instance.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-987654321);
/// // In-place
/// a >>= 1;
/// assert_eq!(a, -493827161);
/// // Also in-place
/// a = a >> 1;
/// assert_eq!(a, -246913581);
/// // Clones the Arbi integer
/// a = &a >> 1;
/// assert_eq!(a, -123456791);
/// ```
///
/// Negative shifts cause a panic:
/// ```should_panic
/// use arbi::Arbi;
/// let _ = Arbi::zero() >> -1;
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl Shr<$bitcount> for &Arbi {
    type Output = Arbi;
    fn shr(self, rhs: $bitcount) -> Arbi {
        let mut ret = self.clone();
        ret >>= rhs;
        ret
    }
}

/// See, for example, [`impl Shr<u32> for &Arbi`](#impl-Shr<u32>-for-%26Arbi).
impl<'a> Shr<&'a $bitcount> for &Arbi {
    type Output = Arbi;
    fn shr(self, rhs: &'a $bitcount) -> Arbi {
        self >> *rhs
    }
}

/// See, for example, [`impl Shr<u32> for &Arbi`](#impl-Shr<u32>-for-%26Arbi).
impl Shr<$bitcount> for Arbi {
    type Output = Arbi;
    fn shr(mut self, rhs: $bitcount) -> Arbi {
        self >>= rhs;
        self
    }
}

/// See, for example, [`impl Shr<u32> for &Arbi`](#impl-Shr<u32>-for-%26Arbi).
impl Shr<&$bitcount> for Arbi {
    type Output = Arbi;
    fn shr(self, rhs: &$bitcount) -> Arbi {
        self >> *rhs
    }
}

/// See, for example, [`impl Shr<u32> for &Arbi`](#impl-Shr<u32>-for-%26Arbi).
impl ShrAssign<$bitcount> for Arbi {
    #[allow(unused_comparisons)]
    fn shr_assign(&mut self, rhs: $bitcount) {
        assert!(rhs >= 0, "Only nonnegative shifts are supported");
        self.arithmetic_rshift(rhs.try_into().unwrap_or(BitCount::MAX));
    }
}

/// See, for example, [`impl Shr<u32> for &Arbi`](#impl-Shr<u32>-for-%26Arbi).
impl ShrAssign<&$bitcount> for Arbi {
    fn shr_assign(&mut self, rhs: &$bitcount) {
        *self >>= *rhs;
    }
}

        )*
    };
}
/* impl_shr_integral! */

for_all_ints!(impl_shr_integral);

#[cfg(test)]
mod test_arithmetic_rshift {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign, BitCount, DDigit, Digit, SDDigit, SDigit};
    // use alloc::vec;

    #[test]
    fn test_mark_a() {
        let mut a = Arbi::from(i128::MIN);
        a.arithmetic_rshift(128);
        assert_eq!(a, -1);

        a.assign(i128::MIN);
        a.arithmetic_rshift(BitCount::MAX);
        assert_eq!(a, -1);
    }

    #[test]
    fn test_mark_b() {
        let mut a = Arbi::from(u128::MAX);
        a.arithmetic_rshift(128);
        assert_eq!(a, 0);

        a.assign(u128::MAX);
        a.arithmetic_rshift(BitCount::MAX);
        assert_eq!(a, 0);
    }

    #[test]
    fn test_correction_needed_with_empty_vec() {
        let mut a = Arbi::from(-207774159847821504_i64);
        a.arithmetic_rshift(58);
        assert_eq!(a, -1);
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn test_correction_needed_with_nonempty_vec() {
        let mut a = Arbi::from(-128965486767644366027235583800544990179_i128);
        a.arithmetic_rshift(1);
        assert_eq!(a, -64482743383822183013617791900272495090_i128);

        a.assign(-99215550095170700947331081298107047598_i128);
        a.arithmetic_rshift(2);
        assert_eq!(a, -24803887523792675236832770324526761900_i128);

        a.assign(-7385860160935551244_i64);
        a.arithmetic_rshift(3);
        assert_eq!(a, -923232520116943906_i64);

        let mut a =
            Arbi::from_digits(vec![0xFFFFFFFF, 0x00000000, 0xFFFFFFFF], true);
        a.arithmetic_rshift(1);
        assert_eq!(
            a,
            Arbi::from_digits(vec![0x80000000, 0x80000000, 0x7fffffff], true)
        );
    }

    #[test]
    fn right_shift_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sdd = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        // let die_sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in i16::MIN..i16::MAX {
            let r = die_sd.sample(&mut rng);
            for shift in 0..(Digit::BITS as BitCount) {
                let mut a = Arbi::from(r);
                a.arithmetic_rshift(shift);
                assert_eq!(
                    a,
                    r >> shift,
                    "Right shift failed r = {r}, shift = {shift}"
                );
            }

            let r = die_sdd.sample(&mut rng);
            for shift in 0..(2 * Digit::BITS as BitCount) {
                let mut a = Arbi::from(r);
                a.arithmetic_rshift(shift);
                assert_eq!(a, r >> shift);
            }

            // let r = die_sqd.sample(&mut rng);
            // for shift in 0..(4 * Digit::BITS as BitCount) {
            //     let mut a = Arbi::from(r);
            //     a.arithmetic_rshift(shift);
            //     assert_eq!(a, r >> shift);
            // }
        }
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn test_correction_with_nonzero_carries_within_loop() {
        // 2-digit number with carries
        let mut a = Arbi::from_digits(vec![0xFFFFFFFF, 1], true);
        assert_eq!(a, -0x1FFFFFFFF_i64);
        a.arithmetic_rshift(1);
        assert_eq!(a, Arbi::from_digits(vec![0, 1], true));
        assert_eq!(a, -0x100000000_i64);

        // 3-digit number with carries
        let mut b = Arbi::from_digits(vec![0xFFFFFFFF, 0xFFFFFFFF, 1], true);
        assert_eq!(b, -0x1FFFFFFFFFFFFFFFF_i128);
        b.arithmetic_rshift(1);
        assert_eq!(b, Arbi::from_digits(vec![0, 0, 1], true));
        assert_eq!(b, -18446744073709551616_i128);
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn test_edge_shifts() {
        let mut a = Arbi::from_digits(vec![0xFFFFFFFF, 0x1], true);
        a.arithmetic_rshift(31);
        assert_eq!(a, Arbi::from_digits(vec![0x4], true));

        let mut b = Arbi::from_digits(vec![0xFFFFFFFF, 0xFFFFFFFF], true);
        b.arithmetic_rshift(33);
        assert_eq!(b, Arbi::from_digits(vec![0x80000000], true));

        let mut c =
            Arbi::from_digits(vec![0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], true);
        c.arithmetic_rshift(65);
        assert_eq!(c, Arbi::from_digits(vec![0x80000000], true));

        let mut d = Arbi::from_digits(vec![0x1], true);
        d.arithmetic_rshift(1);
        assert_eq!(d, Arbi::from_digits(vec![0x1], true));
    }

    #[test]
    fn test_right_shift_to_zero_more_than_max_bits() {
        let a = Arbi::from(123456789) >> (Arbi::MAX_BITS + 1);
        assert_eq!(a, 0);

        let a = Arbi::from(-123456789) >> (Arbi::MAX_BITS + 1);
        assert_eq!(a, -1);
    }

    #[test]
    fn test_right_shift_to_zero_max_bits() {
        let a = Arbi::from(123456789) >> Arbi::MAX_BITS;
        assert_eq!(a, 0);

        let a = Arbi::from(-123456789) >> Arbi::MAX_BITS;
        assert_eq!(a, -1);
    }

    #[test]
    #[should_panic = "Only nonnegative shifts are supported"]
    fn test_negative_shift_panics() {
        let _ = Arbi::zero() >> -1;
    }

    #[test]
    fn test_right_shift_assign() {
        let mut zero = Arbi::zero();
        zero >>= 1;
        assert_eq!(zero, 0);

        let mut a = Arbi::from(Digit::MAX as DDigit * 2);
        a >>= Digit::BITS as BitCount;
        assert_eq!(a, 1);

        let mut a = Arbi::from(3619132862646584885328_u128);
        a >>= 1;
        assert_eq!(a, 1809566431323292442664_u128);
        a >>= 21;
        assert_eq!(a, 862868514691969_u64);
        a >>= 50;
        assert_eq!(a, 0);

        let mut a = Arbi::from(16);
        a >>= 3;
        assert_eq!(a, 2);

        let mut a = Arbi::from(4);
        a >>= 4;
        assert_eq!(a, 0);
    }

    #[test]
    fn test_right_shift() {
        assert_eq!(Arbi::zero() >> 1, 0);
        assert_eq!(Arbi::from(Digit::MAX as DDigit * 2) >> Digit::BITS, 1);
        assert_eq!(
            Arbi::from_str_base(
                "3619132862646584885328",
                10.try_into().unwrap()
            )
            .unwrap()
                >> 1,
            Arbi::from_str_base(
                "1809566431323292442664",
                10.try_into().unwrap()
            )
            .unwrap()
        );

        let pos = Arbi::from(16);
        assert_eq!(&pos >> 3, 2);
        assert_eq!(&pos >> 0, 16);
        assert_eq!(&pos >> (Digit::BITS * 2), 0);

        let neg = Arbi::from(-16);
        assert_eq!(&neg >> 2, -4);
        assert_eq!(&neg >> 0, -16);
        assert_eq!(&neg >> (Digit::BITS * 2), -1);

        let mon = Arbi::neg_one();
        assert_eq!(&mon >> 0, -1);
        assert_eq!((&mon) >> 1, -1);
        assert_eq!(&mon >> (Digit::BITS + 1), -1);
    }

    #[test]
    fn test_right_shift_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for i in i16::MIN..i16::MAX {
            let r: SDDigit = die.sample(&mut rng);

            for shift in 0..=((2 * Digit::BITS) - 1) {
                assert_eq!(
                    Arbi::from(r) >> shift,
                    r >> shift,
                    "Shift = {}, r = {}, Arbi = {}, i = {}",
                    shift,
                    r,
                    Arbi::from(r) >> shift,
                    i
                );
            }
        }
    }
}
