/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::macros::for_all_ints;
use crate::{Arbi, BitCount, Digit};
use core::ops::{Shl, ShlAssign};

impl Arbi {
    pub(crate) fn dslice_lshift_inplace(
        digits: &mut [Digit],
        start_idx: usize,
        size: usize,
        bit_shift: u32,
    ) -> Digit {
        debug_assert!(size > 0);
        debug_assert!(digits.len() >= start_idx.saturating_add(size));
        debug_assert!((1..Digit::BITS).contains(&bit_shift));
        let com_bit_shift = Digit::BITS - bit_shift;
        let shifted_out = digits[size - 1] >> com_bit_shift;
        let mut lower = digits[size - 1];
        let mut upper = lower << bit_shift;
        for i in (1..size).rev() {
            lower = digits[i - 1];
            digits[start_idx + i] = upper | (lower >> com_bit_shift);
            upper = lower << bit_shift;
        }
        digits[start_idx] = upper;
        shifted_out
    }

    /// Shift `self` left by `bits` bits.
    /// Equivalent to `self` * (2 ** bits).
    pub(crate) fn lshift(&mut self, bits: BitCount) {
        if self.is_zero() {
            return;
        }
        let dig_shift = (bits / Digit::BITS as BitCount)
            .try_into()
            .unwrap_or(usize::MAX);
        let bit_shift = (bits % Digit::BITS as BitCount) as u32;
        let old_size = self.size();
        let new_size = old_size
            .saturating_add(dig_shift)
            .saturating_add(usize::from(bit_shift != 0));
        self.vec.resize(new_size, 0);
        if bit_shift == 0 {
            self.vec.copy_within(0..old_size, dig_shift);
        } else {
            self.vec[dig_shift + old_size] = Self::dslice_lshift_inplace(
                &mut self.vec,
                dig_shift,
                old_size,
                bit_shift,
            );
        }
        self.vec[..dig_shift].fill(0);
        self.trim();
    }
}

/* !impl_shl_integral */
macro_rules! impl_shl_integral {
    ($($bitcount:ty),*) => {
        $(

/// Return an `Arbi` integer representing this integer left-shifted `shift` bit
/// positions with vacated bits zero-filled.
///
/// Mathematically, the value of the resulting integer is
/// \\[
///     x \times 2^{\text{shift}}
/// \\]
/// where \\( x \\) is the big integer.
///
/// The right-hand-side (RHS) of a left shift operation can be a nonnegative
/// value of any primitive integer type.
///
/// # Panics
/// - Panics if `rhs` is negative.
/// - Panics if the result of the operation exceeds `Vec`'s limits.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// assert_eq!(Arbi::zero() << 1, 0);
/// assert_eq!(0 << 1, 0);
///
/// let mut a = Arbi::neg_one();
///
/// a <<= 0;
/// assert_eq!(a, -1);
/// assert_eq!(a, -1 << 0);
///
/// a <<= 1; // in-place
/// assert_eq!(a, -2);
/// assert_eq!(a, -1 << 1);
///
/// a = a << 1; // in-place
/// assert_eq!(a, -4);
/// assert_eq!(a, -1 << 2);
///
/// a = &a << 1; // clones (currently)
/// assert_eq!(a, -8);
/// assert_eq!(a, -1 << 3);
/// ```
///
/// Negative RHS values cause a panic:
/// ```should_panic
/// use arbi::Arbi;
/// let _ = Arbi::zero() << -1;
/// ```
///
/// This panics because it would exceed `Vec`'s limits:
/// ```should_panic
/// use arbi::Arbi;
/// let _ = Arbi::one() << Arbi::MAX_BITS;
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl Shl<$bitcount> for &Arbi {
    type Output = Arbi;
    fn shl(self, rhs: $bitcount) -> Arbi {
        let mut ret = self.clone();
        ret <<= rhs;
        ret
    }
}

/// See, for example, [`Shl<u32> for &Arbi`](#impl-Shl<u32>-for-%26Arbi).
impl<'a> Shl<&'a $bitcount> for &Arbi {
    type Output = Arbi;
    fn shl(self, rhs: &'a $bitcount) -> Arbi {
        self << *rhs
    }
}

/// See, for example, [`Shl<u32> for &Arbi`](#impl-Shl<u32>-for-%26Arbi).
impl Shl<$bitcount> for Arbi {
    type Output = Arbi;
    fn shl(mut self, rhs: $bitcount) -> Arbi {
        self <<= rhs;
        self
    }
}

/// See, for example, [`Shl<u32> for &Arbi`](#impl-Shl<u32>-for-%26Arbi).
impl Shl<&$bitcount> for Arbi {
    type Output = Arbi;
    fn shl(self, rhs: &$bitcount) -> Arbi {
        self << *rhs
    }
}

/// See, for example, [`Shl<u32> for &Arbi`](#impl-Shl<u32>-for-%26Arbi).
impl ShlAssign<$bitcount> for Arbi {
    #[allow(unused_comparisons)]
    fn shl_assign(&mut self, rhs: $bitcount) {
        assert!(rhs >= 0, "Only nonnegative shifts are supported");
        self.lshift(rhs.try_into().unwrap_or(BitCount::MAX));
    }
}

/// See, for example, [`Shl<u32> for &Arbi`](#impl-Shl<u32>-for-%26Arbi).
impl ShlAssign<&$bitcount> for Arbi {
    fn shl_assign(&mut self, rhs: &$bitcount) {
        *self <<= *rhs
    }
}

        )*
    };
}
/* impl_shl_integral! */

for_all_ints!(impl_shl_integral);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitCount, DDigit};

    // On rustc < 1.65, fails with message, "memory allocation of {isize::MAX as
    // usize + 1} bytes failed", but in 1.65 (MSRV) and later, does not.
    #[test]
    #[should_panic = "capacity overflow"] // From `Vec`
    fn test_large_shift_panics_max_bits() {
        let one = Arbi::one();
        let _ = one << Arbi::MAX_BITS;
    }

    #[test]
    #[should_panic = "Only nonnegative shifts are supported"]
    fn test_negative_shift_panics() {
        let _ = Arbi::zero() << -1;
    }

    #[test]
    fn test_left_shift_zero() {
        assert_eq!(Arbi::zero() << 1 as BitCount, 0);
        assert_eq!(Arbi::zero() << Digit::BITS as BitCount, 0);
        assert_eq!(Arbi::zero() << 0 as BitCount, 0);
    }

    #[test]
    fn test_left_shift_assign_zero() {
        let mut zero: Arbi;

        zero = Arbi::zero();
        zero <<= 1 as BitCount;
        assert_eq!(zero, 0);

        zero = Arbi::zero();
        zero <<= Digit::BITS as BitCount;
        assert_eq!(zero, 0);

        zero = Arbi::zero();
        zero <<= 0 as BitCount;
        assert_eq!(zero, 0);
    }

    #[test]
    fn test_left_shift_misc() {
        assert_eq!(Arbi::from(4) << 2 as BitCount, 16);
        assert_eq!(Arbi::from(-4) << 2 as BitCount, -16);
        assert_eq!(Arbi::from(4) << 0 as BitCount, 4);
        assert_eq!(Arbi::from(-4) << 0 as BitCount, -4);
    }

    #[test]
    fn test_left_shift_assign_misc() {
        let mut a: Arbi;

        a = Arbi::from(4);
        a <<= 2 as BitCount;
        assert_eq!(a, 16);

        a = Arbi::from(-4);
        a <<= 2 as BitCount;
        assert_eq!(a, -16);

        a = Arbi::from(4);
        a <<= 0 as BitCount;
        assert_eq!(a, 4);

        a = Arbi::from(-4);
        a <<= 0 as BitCount;
        assert_eq!(a, -4);
    }

    #[test]
    fn test_left_shift_powers_of_2_in_digit() {
        let one = Arbi::one();
        for i in 0..(Digit::BITS as BitCount * 2) {
            assert_eq!(&one << i, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_left_shift_assign_powers_of_2_in_digit() {
        for i in 0..(Digit::BITS as BitCount * 2) {
            let mut one = Arbi::one();
            one <<= i;
            assert_eq!(one, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_lshift() {
        let mut one = Arbi::one();
        let mut one_prim: u128 = 1;
        for i in (1 as BitCount)..(128 as BitCount) {
            assert_eq!(Arbi::one() << i, 1_u128 << i);
            assert_eq!(one, one_prim, "i = {}", i);
            one <<= 1 as BitCount;
            one_prim <<= 1 as BitCount;
        }
    }
}
