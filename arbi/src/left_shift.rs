/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! From ISO/IEC 2020 (C++), "\[t\]he value of `E1 << E2` is the unique value
//! congruent to `E1 * 2^{E2}` modulo `2^{N}` , where `N` is the width of the
//! type of the result... E1 is left-shifted E2 bit positions; vacated bits are
//! zero-filled."
//!
//! This is consistent with Rust's built-in behavior for left-shifting by an
//! unsigned integer value.

use crate::{Arbi, BitCount, Digit};
use core::ops::{Shl, ShlAssign};

/* !impl_shl_unsigned_integral */
macro_rules! impl_shl_unsigned_integral {
    // NOTE: bitcount must be an unsigned type with width <= that of BitCount
    ($($bitcount:ty => ($lshift_name:ident, $lshift_name_inplace:ident, $ubitcount:ty)),*) => {
        $(

impl Arbi {
    fn $lshift_name_inplace(&mut self, n_bits: $bitcount) {
        #[allow(unused_comparisons)]
        if n_bits < 0 {
            panic!("Only nonnegative shifts are supported");
        }
        let n_bits: $ubitcount = n_bits as $ubitcount;
        if n_bits as BitCount > Arbi::MAX_BITS {
            panic!("capacity overflow!");
        }
        if self.is_zero() || n_bits == 0 {
            return;
        }
        let digit_shift: usize = (n_bits / Digit::BITS as $ubitcount) as usize;
        let bit_shift: usize =
            (n_bits % Digit::BITS as $ubitcount) as usize;
        let compl_bit_shift = Digit::BITS as usize - bit_shift;
        let size_self = self.size();
        let size_result =
            size_self + digit_shift + if bit_shift > 0 { 1 } else { 0 };
        if size_result < size_self {
            panic!("Result size exceeds SIZE_MAX");
        }
        self.vec.resize(size_result, 0);
        if digit_shift > 0 {
            for i in (0..size_self).rev() {
                self.vec[i + digit_shift] = self.vec[i];
            }
            for i in 0..digit_shift {
                self.vec[i] = 0;
            }
        }
        if bit_shift > 0 {
            let mut carry = 0;
            for i in digit_shift..size_result {
                let temp = self.vec[i];
                self.vec[i] = (temp << bit_shift) | carry;
                carry = temp >> compl_bit_shift;
            }
            assert!(carry == 0);
        }
        self.trim();
    }
}

/// See [`Shl<u128> for &Arbi`](#impl-Shl<u128>-for-%26Arbi).
impl Shl<$bitcount> for Arbi {
    type Output = Arbi;

    fn shl(mut self, rhs: $bitcount) -> Arbi {
        self.$lshift_name_inplace(rhs);
        self
    }
}

/// See [`Shl<u128> for &Arbi`](#impl-Shl<u128>-for-%26Arbi).
impl ShlAssign<$bitcount> for Arbi {
    fn shl_assign(&mut self, rhs: $bitcount) {
        self.$lshift_name_inplace(rhs);
    }
}

/// Return an `Arbi` integer representing this integer left-shifted `shift` bit
/// positions with vacated bits zero-filled.
///
/// Mathematically, the value of the resulting integer is
/// \\[
///     x \times 2^{\text{shift}}
/// \\]
/// where \\( x \\) is the big integer.
///
/// This is consistent with Rust's built-in behavior for left-shifting integers
/// by an unsigned integer value.
///
/// The right-hand-side (RHS) of a left shift operation can be a value of type:
/// - `BitCount`
/// - `usize`
/// - `u32`
/// - `i32`
///
/// While `i32` is supported, please note that negative RHS values cause a
/// panic.
///
/// # Panics
/// - Panics if `rhs` is an `i32` and its value is negative.
/// - Panics if the result of the operation exceeds `Vec`'s limits.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// assert_eq!(Arbi::zero() << 1, 0);
/// assert_eq!(0 << 1, 0);
///
/// let mut a = Arbi::from(-1);
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
/// let _ = Arbi::from(1) << Arbi::MAX_BITS;
/// ```
///
/// ## Complexity
/// \\( O(n) \\)
impl Shl<$bitcount> for &Arbi {
    type Output = Arbi;

    fn shl(self, rhs: $bitcount) -> Arbi {
        let mut ret = self.clone();
        ret.$lshift_name_inplace(rhs);
        ret
    }
}

/// See [`Shl<u128> for &Arbi`](#impl-Shl<u128>-for-%26Arbi).
impl<'a> Shl<&'a $bitcount> for Arbi {
    type Output = Arbi;

    fn shl(mut self, rhs: &'a $bitcount) -> Arbi {
        self.$lshift_name_inplace(*rhs);
        self
    }
}

/// See [`Shl<u128> for &Arbi`](#impl-Shl<u128>-for-%26Arbi).
impl<'a> ShlAssign<&'a $bitcount> for Arbi {
    fn shl_assign(&mut self, rhs: &'a $bitcount) {
        self.$lshift_name_inplace(*rhs)
    }
}

        )*
    };
}
/* impl_shl_unsigned_integral! */

impl_shl_unsigned_integral!(
    BitCount => (lshift_bitcount, lshift_bitcount_inplace, BitCount),
    usize => (lshift_usize, lshift_usize_inplace, usize),
    u32 => (lshift_u32, lshift_u32_inplace, u32),
    i32 => (lshift_i32, lshift_i32_inplace, u32)
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitCount, DDigit};

    #[test]
    #[should_panic = "capacity overflow!"] // Internal guard
    fn test_large_shift_panics_more_than_max_bits() {
        let one = Arbi::from(1);
        let _ = one << (Arbi::MAX_BITS + 1);
    }

    #[test]
    #[should_panic = "capacity overflow"] // From `Vec`
    fn test_large_shift_panics_max_bits() {
        let one = Arbi::from(1);
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
        let one = Arbi::from(1);
        for i in 0..(Digit::BITS as BitCount * 2) {
            assert_eq!(&one << i, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_left_shift_assign_powers_of_2_in_digit() {
        for i in 0..(Digit::BITS as BitCount * 2) {
            let mut one = Arbi::from(1);
            one <<= i;
            assert_eq!(one, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_lshift() {
        let mut one = Arbi::from(1);
        let mut one_prim: u128 = 1;
        for i in (1 as BitCount)..(128 as BitCount) {
            assert_eq!(Arbi::from(1) << i, 1_u128 << i);
            assert_eq!(one, one_prim, "i = {}", i);
            one <<= 1 as BitCount;
            one_prim <<= 1 as BitCount;
        }
    }
}
