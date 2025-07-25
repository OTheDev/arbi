/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::BitCount;

#[allow(dead_code)]
pub(crate) trait UnsignedUtilities: Sized {
    fn uaddc(r: &mut Self, a: Self, b: Self, carry: &mut u8);
    fn usubb(r: &mut Self, a: Self, b: Self, borrow: &mut u8);
    fn uadd_overflow(r: &mut Self, a: Self, b: Self) -> bool;
    fn usub_overflow(r: &mut Self, a: Self, b: Self) -> bool;
    fn umul_overflow(r: &mut Self, a: Self, b: Self) -> bool;
    /// Return the number of bits required to represent a value of type Self,
    /// where Self is an unsigned integral type.
    fn bit_length(value: Self) -> u8;
    /// Return the number of leading zero bits in nonzero unsigned integral `v`,
    /// starting from the MSB.
    fn clz(value: Self) -> u8;
    /// Any integer with absolute value less than 2 ** 53 can be exactly
    /// represented in an IEEE 754 double. An n-bit unsigned integer can
    /// represent values in the range [0, 2 ** n - 1].
    ///
    /// Method 1:
    ///     - `return bit_length(value) <= double_precision;`
    ///     - `[double_precision is 53]``
    ///
    /// Method 2:
    ///     - `return value <= dbl_max_int;`
    ///     - `[dbl_max_int is 2 ** 53]`
    fn has_double_exact(value: Self) -> bool;
    fn div_ceil_(x: Self, y: Self) -> Self;
    fn ilog2_(v: Self) -> u8;
    fn ilog_(v: Self, base: Self) -> u32;
    fn ilog10_(v: Self) -> u32;
    /// Integer square root using binary search.
    /// Returns the largest integer y such that y * y <= x.
    fn isqrt_(self) -> Self;
}

/* !impl_unsigned_utilities */
macro_rules! impl_unsigned_utilities {
    ($($t:ty),*) => {
        $(

impl UnsignedUtilities for $t {
    fn uaddc(r: &mut Self, a: Self, b: Self, carry: &mut u8) {
        let temp = a.wrapping_add(*carry as $t);
        *r = b.wrapping_add(temp);
        *carry = if *r < b || temp < a { 1 } else { 0 };
    }

    fn usubb(r: &mut Self, a: Self, b: Self, borrow: &mut u8) {
        let temp = a.wrapping_sub(b);
        *r = temp.wrapping_sub(*borrow as $t);
        *borrow = if *r > temp || temp > a { 1 } else { 0 };
    }

    fn uadd_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_add(b);
        return *r < a;
    }

    fn usub_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_sub(b);
        return a < b;
    }

    fn umul_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_mul(b);
        return if a != 0 { true } else { false } && *r / a != b;
    }

    fn bit_length(number: Self) -> u8 {
        if number == 0 {
            1
        } else {
            <$t>::BITS as u8 - number.leading_zeros() as u8
        }
    }

    fn ilog2_(v: Self) -> u8 {
        if v <= 0 {
            panic!("ilog2_(): value must be positive: {}", v)
        }
        Self::bit_length(v) - 1
    }

    fn ilog_(v: Self, base: Self) -> u32 {
        if v < 1 || base < 2 {
            panic!("ilog_(): value ({}) must be positive and base ({}) >= 2", v, base);
        }
        let mut ret = 0;
        let mut cur = v;
        while cur >= base {
            cur /= base;
            ret += 1;
        }
        ret
    }

    fn ilog10_(v: Self) -> u32 {
        Self::ilog_(v, 10)
    }

    fn clz(v: Self) -> u8 {
        let width = Self::BITS as u8;
        width - Self::bit_length(v)
    }

    fn has_double_exact(value: Self) -> bool {
        const DBL_MAX_INT: u64 = 0x20000000000000; // 2 ** 53
        if Self::BITS >= u64::BITS {
            value <= DBL_MAX_INT as Self
        } else {
            value as u64 <= DBL_MAX_INT
        }
    }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// positive infinity.
    ///
    /// # Panics
    /// This function will panic if `rhs` is zero.
    ///
    /// # Examples
    /// ```ignore
    /// assert_eq!(u64::div_ceil_(9, 5), 2);
    /// ```
    fn div_ceil_(x: Self, y: Self) -> Self {
        if x == 0 {
            0
        } else {
            1 + (x - 1) / y
        }
    }

    fn isqrt_(self) -> Self {
        let x = self;

        let mut l = 0;
        let mut r = x;
        let mut result = 0;

        while l <= r {
            let m = l + (r - l) / 2;

            let (square, overflow) = m.overflowing_mul(m);

            if !overflow && square <= x {
                result = m;
                l = m + 1;  // Try to find a bigger one
            } else {
                r = m - 1;
            }
        }

        result
    }
}

        )*
    }
}
/* impl_unsigned_utilities! */

impl_unsigned_utilities!(u8, u16, u32, u64, u128, usize);

pub(crate) const fn div_ceil_usize(x: usize, y: usize) -> usize {
    if x == 0 {
        0
    } else {
        1 + (x - 1) / y
    }
}

#[allow(dead_code)]
pub(crate) const fn div_ceil_bitcount(x: BitCount, y: BitCount) -> BitCount {
    if x == 0 {
        0
    } else {
        1 + (x - 1) / y
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uaddc() {
        let a = 255u8;
        let b = 1u8;
        let mut carry = 0u8;

        let mut result = 0;
        u8::uaddc(&mut result, a, b, &mut carry);
        assert_eq!(result, 0);
        assert_eq!(carry, 1);

        let a = 100u32;
        let b = 200u32;
        let mut carry = 0u8;

        let mut result = 0;
        u32::uaddc(&mut result, a, b, &mut carry);
        assert_eq!(result, 300);
        assert_eq!(carry, 0);
    }

    #[test]
    fn test_usubb() {
        let a = 0u8;
        let b = 1u8;
        let mut borrow = 0u8;

        let mut result = 0;
        u8::usubb(&mut result, a, b, &mut borrow);
        assert_eq!(result, 255);
        assert_eq!(borrow, 1);

        let a = 300u32;
        let b = 200u32;
        let mut borrow = 0u8;

        let mut result = 0;
        u32::usubb(&mut result, a, b, &mut borrow);
        assert_eq!(result, 100);
        assert_eq!(borrow, 0);
    }

    #[test]
    fn test_uadd_overflow() {
        let a = u32::MAX;
        let b = 1u32;

        let mut result = 0;
        let overflow = u32::uadd_overflow(&mut result, a, b);
        assert_eq!(result, 0);
        assert!(overflow);
        assert_eq!(a.wrapping_add(b), result);

        let a = 10u32;
        let b = 20u32;

        let mut result = 0;
        let overflow = u32::uadd_overflow(&mut result, a, b);
        assert_eq!(result, 30);
        assert!(!overflow);
        assert_eq!(a.wrapping_add(b), result);
    }

    #[test]
    fn test_usub_overflow() {
        let a = 10u32;
        let b = 20u32;

        let mut result = 0;
        let overflow = u32::usub_overflow(&mut result, a, b);
        assert_eq!(result, u32::MAX - 9);
        assert!(overflow);
        assert_eq!(a.wrapping_sub(b), result);

        let a = 30u32;
        let b = 10u32;

        let mut result = 0;
        let overflow = u32::usub_overflow(&mut result, a, b);
        assert_eq!(result, 20);
        assert!(!overflow);
        assert_eq!(a.wrapping_sub(b), result);
    }

    #[test]
    fn test_umul_overflow() {
        let a = u32::MAX / 2 + 1;
        let b = 2u32;

        let mut result = 0;
        let overflow = u32::umul_overflow(&mut result, a, b);
        assert_eq!(result, 0);
        assert!(overflow);
        assert_eq!(a.wrapping_mul(b), result);

        let a = 0u32;
        let b = 123u32;

        let mut result = 0;
        let overflow = u32::umul_overflow(&mut result, a, b);
        assert_eq!(result, 0);
        assert!(!overflow);
        assert_eq!(a.wrapping_mul(b), result);
    }
}

#[cfg(test)]
mod test_other {
    use super::*;

    #[test]
    fn test_bit_length() {
        assert_eq!(u32::bit_length(0), 1);
        assert_eq!(u32::bit_length(8), 4);
        assert_eq!(u32::bit_length(255), 8);
    }

    #[test]
    fn test_clz() {
        assert_eq!(u32::clz(1), 31);
        assert_eq!(u32::clz(8), 28);
    }

    #[test]
    fn test_has_double_exact() {
        assert!(u64::has_double_exact(0x20000000000000 - 1));
        assert!(u64::has_double_exact(0x20000000000000));
        assert!(!u64::has_double_exact(0x20000000000000 + 1));
    }

    #[test]
    fn test_div_ceil() {
        assert_eq!(u32::div_ceil_(5, 2), 3);
        assert_eq!(u32::div_ceil_(10, 5), 2);
        assert_eq!(u32::div_ceil_(11, 5), 3);
    }

    enum BinOp {
        Add,
        Sub,
        Mul,
    }

    fn test_binop_overflow_(op: BinOp) {
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };
        use crate::{Arbi, DDigit};

        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(DDigit::MIN, DDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) = (die.sample(&mut rng), die.sample(&mut rng));
            let (a, b) = (Arbi::from(a_in), Arbi::from(b_in));
            let mut e: DDigit = 0;
            match op {
                BinOp::Add => {
                    let overflow = DDigit::uadd_overflow(&mut e, a_in, b_in);
                    if !overflow {
                        assert_eq!(a + b, e);
                    }
                }
                BinOp::Sub => {
                    let overflow = DDigit::usub_overflow(&mut e, a_in, b_in);
                    if !overflow {
                        assert_eq!(a - b, e);
                    }
                }
                BinOp::Mul => {
                    let overflow = DDigit::umul_overflow(&mut e, a_in, b_in);
                    if !overflow {
                        assert_eq!(a * b, e);
                    }
                }
            }
        }
    }

    #[test]
    fn test_binop_overflow() {
        test_binop_overflow_(BinOp::Add);
        test_binop_overflow_(BinOp::Sub);
        test_binop_overflow_(BinOp::Mul);
    }
}
