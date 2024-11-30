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

use crate::{Arbi, Digit};
use core::ops::{Shl, ShlAssign};

/* !impl_shl_unsigned_integral */
macro_rules! impl_shl_unsigned_integral {
    // NOTE: bitcount must be an unsigned type with width <= that of usize
    ($($bitcount:ty => ($lshift_name:ident, $lshift_name_inplace:ident)),*) => {
        $(

impl Arbi {
    fn $lshift_name_inplace(&mut self, n_bits: $bitcount) {
        let n_bits = n_bits as usize;

        if self.is_zero() || n_bits == 0 {
            return;
        }

        let digit_shift: usize = n_bits / Digit::BITS as usize;
        let bit_shift: usize = n_bits % Digit::BITS as usize;
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

/// See [`Shl<usize> for &Arbi`](#impl-Shl<usize>-for-%26Arbi).
impl Shl<$bitcount> for Arbi {
    type Output = Arbi;

    fn shl(mut self, rhs: $bitcount) -> Arbi {
        self.$lshift_name_inplace(rhs);
        self
    }
}

/// See [`Shl<usize> for &Arbi`](#impl-Shl<usize>-for-%26Arbi).
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
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// assert_eq!(Arbi::zero() << 1_usize, 0);
/// assert_eq!(0 << 1, 0);
///
/// let mut a = Arbi::from(-1);
///
/// a <<= 0_usize;
/// assert_eq!(a, -1);
/// assert_eq!(a, -1 << 0);
///
/// a <<= 1_usize; // in-place
/// assert_eq!(a, -2);
/// assert_eq!(a, -1 << 1);
///
/// a = a << 1_usize; // in-place
/// assert_eq!(a, -4);
/// assert_eq!(a, -1 << 2);
///
/// a = &a << 1_usize; // clones (currently)
/// assert_eq!(a, -8);
/// assert_eq!(a, -1 << 3);
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

/// See [`Shl<usize> for &Arbi`](#impl-Shl<usize>-for-%26Arbi).
impl<'a> Shl<&'a $bitcount> for Arbi {
    type Output = Arbi;

    fn shl(mut self, rhs: &'a $bitcount) -> Arbi {
        self.$lshift_name_inplace(*rhs);
        self
    }
}

/// See [`Shl<usize> for &Arbi`](#impl-Shl<usize>-for-%26Arbi).
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
    usize => (lshift_usize, lshift_usize_inplace),
    u32 => (lshift_u32, lshift_u32_inplace)
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DDigit;

    #[test]
    fn test_left_shift_zero() {
        assert_eq!(Arbi::zero() << 1_usize, 0);
        assert_eq!(Arbi::zero() << Digit::BITS as usize, 0);
        assert_eq!(Arbi::zero() << 0_usize, 0);
    }

    #[test]
    fn test_left_shift_assign_zero() {
        let mut zero: Arbi;

        zero = Arbi::zero();
        zero <<= 1_usize;
        assert_eq!(zero, 0);

        zero = Arbi::zero();
        zero <<= Digit::BITS;
        assert_eq!(zero, 0);

        zero = Arbi::zero();
        zero <<= 0_usize;
        assert_eq!(zero, 0);
    }

    #[test]
    fn test_left_shift_misc() {
        assert_eq!(Arbi::from(4) << 2_usize, 16);
        assert_eq!(Arbi::from(-4) << 2_usize, -16);
        assert_eq!(Arbi::from(4) << 0_usize, 4);
        assert_eq!(Arbi::from(-4) << 0_usize, -4);
    }

    #[test]
    fn test_left_shift_assign_misc() {
        let mut a: Arbi;

        a = Arbi::from(4);
        a <<= 2_usize;
        assert_eq!(a, 16);

        a = Arbi::from(-4);
        a <<= 2_usize;
        assert_eq!(a, -16);

        a = Arbi::from(4);
        a <<= 0_usize;
        assert_eq!(a, 4);

        a = Arbi::from(-4);
        a <<= 0_usize;
        assert_eq!(a, -4);
    }

    #[test]
    fn test_left_shift_powers_of_2_in_digit() {
        let one = Arbi::from(1);
        for i in 0..(Digit::BITS as usize * 2) {
            assert_eq!(&one << i, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_left_shift_assign_powers_of_2_in_digit() {
        for i in 0..(Digit::BITS as usize * 2) {
            let mut one = Arbi::from(1);
            one <<= i;
            assert_eq!(one, (1 as DDigit) << i);
        }
    }

    #[test]
    fn test_lshift() {
        let mut one = Arbi::from(1);
        let mut one_prim: u128 = 1;
        for i in 1_usize..128_usize {
            assert_eq!(Arbi::from(1) << i, 1_u128 << i);
            assert_eq!(one, one_prim, "i = {}", i);
            one <<= 1_usize;
            one_prim <<= 1_usize;
        }
    }
}
