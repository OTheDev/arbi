/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::comparisons_integral::CompareWith;
use crate::uints::UnsignedUtilities;
use crate::{Arbi, Digit};
use crate::{QDigit, SQDigit};
use alloy_primitives::{I256, U256};
use core::cmp::Ordering;
use core::ops::Shr;
use rand::Rng;

#[cfg(not(target_pointer_width = "64"))]
use crate::util::test::{get_uniform_die, Uniform};

// TODO: technically this code can be used for impl UnsignedUtilities for X,
// where X is any unsigned type. Evaluate performance for more maintainable
// code.
impl UnsignedUtilities for U256 {
    fn uaddc(r: &mut Self, a: Self, b: Self, carry: &mut u8) {
        let temp = a.wrapping_add(Self::from(*carry));
        *r = b.wrapping_add(temp);
        *carry = if *r < b || temp < a { 1 } else { 0 };
    }

    fn usubb(r: &mut Self, a: Self, b: Self, borrow: &mut u8) {
        let temp = a.wrapping_sub(b);
        *r = temp.wrapping_sub(Self::from(*borrow));
        *borrow = if *r > temp || temp > a { 1 } else { 0 };
    }

    fn uadd_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_add(b);
        *r < a
    }

    fn usub_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_sub(b);
        a < b
    }

    fn umul_overflow(r: &mut Self, a: Self, b: Self) -> bool {
        *r = a.wrapping_mul(b);
        return if a != Self::from(0u8) { true } else { false } && *r / a != b;
    }

    fn bit_length(number: Self) -> u32 {
        if number == Self::from(0u8) {
            1
        } else {
            Self::BITS as u32 - number.leading_zeros() as u32
        }
    }

    fn clz(v: Self) -> u32 {
        v.leading_zeros() as u32
    }

    fn ilog2_(v: Self) -> u32 {
        if v <= Self::from(0u8) {
            panic!("ilog2_(): value must be positive: {}", v)
        }
        Self::bit_length(v) - 1
    }

    fn ilog_(v: Self, base: u32) -> u32 {
        let base = Self::from(base as u8);
        if v < Self::from(1u8) || base < Self::from(2u8) {
            panic!(
                "ilog_(): value ({}) must be positive and base ({}) >= 2",
                v, base
            );
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

    fn has_double_exact(value: Self) -> bool {
        const DBL_MAX_INT: u64 = 0x20000000000000; // 2 ** 53
        if Self::BITS as u32 >= u64::BITS {
            value <= Self::try_from(DBL_MAX_INT).unwrap()
        } else {
            u64::try_from(value).unwrap() <= DBL_MAX_INT
        }
    }

    fn div_ceil_(x: Self, y: Self) -> Self {
        if x == Self::from(0u8) {
            Self::from(0u8)
        } else {
            Self::from(1u8) + (x - Self::from(1u8)) / y
        }
    }

    fn isqrt_(self) -> Self {
        let x = self;
        let mut l = Self::from(0u8);
        let mut r = x;
        let mut result = Self::from(0u8);
        while l <= r {
            let m = l + (r - l) / Self::from(2u8);
            let (square, overflow) = m.overflowing_mul(m);
            if !overflow && square <= x {
                result = m;
                l = m + Self::from(1u8);
            } else {
                r = m - Self::from(1u8);
            }
        }
        result
    }
}

impl From<U256> for Arbi {
    fn from(value: U256) -> Self {
        type UnsignedT = U256;

        let mut uvalue: UnsignedT;
        let mut x = Arbi::zero();
        if value.is_zero() {
            return x;
        } else {
            uvalue = value;
            x.neg = false;
        }

        let mut size = 1;
        let mut temp: UnsignedT = uvalue;

        loop {
            temp = temp.shr(Digit::BITS);
            if temp.is_zero() {
                break;
            }
            size += 1;
        }

        x.vec.resize(size, 0);

        let mut i = 0;
        while !uvalue.is_zero() {
            x.vec[i] = uvalue.as_limbs()[0] as Digit;
            uvalue = uvalue.shr(Digit::BITS);
            i += 1;
        }

        x
    }
}

impl From<&U256> for Arbi {
    fn from(value: &U256) -> Self {
        Arbi::from(*value)
    }
}

impl From<I256> for Arbi {
    fn from(value: I256) -> Self {
        type UnsignedT = U256;

        let mut uvalue: UnsignedT;
        let mut x = Arbi::zero();
        if value.is_zero() {
            return x;
        } else if value.is_negative() {
            uvalue =
                UnsignedT::ZERO.wrapping_sub(UnsignedT::wrapping_from(value));
            x.neg = true;
        } else {
            uvalue = UnsignedT::wrapping_from(value);
            x.neg = false;
        }

        let mut size = 1;
        let mut temp: UnsignedT = uvalue;

        loop {
            temp = temp.shr(Digit::BITS);
            if temp.is_zero() {
                break;
            }
            size += 1;
        }

        x.vec.resize(size, 0);

        let mut i = 0;
        while !uvalue.is_zero() {
            x.vec[i] = uvalue.as_limbs()[0] as Digit;
            uvalue = uvalue.shr(Digit::BITS);
            i += 1;
        }

        x
    }
}

impl From<&I256> for Arbi {
    fn from(value: &I256) -> Self {
        Arbi::from(*value)
    }
}

// For U256. TODO: not ideal
pub(crate) fn get_uniform_u256_die<R: Rng>(
    min_inclusive: U256,
    max_inclusive: U256,
    rng: &mut R,
) -> U256 {
    if min_inclusive == max_inclusive {
        return min_inclusive;
    }

    let range = max_inclusive - min_inclusive;

    if range == U256::MAX {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        return U256::from_be_bytes(bytes);
    }

    let range_plus_one = range + U256::from(1);

    loop {
        // Random U256
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        let candidate = U256::from_be_bytes(bytes);

        // Rejection sampling
        let multiplier = U256::MAX / range_plus_one;
        let limit = multiplier * range_plus_one;

        if candidate < limit {
            let result = candidate % range_plus_one;
            return min_inclusive + result;
        }
    }
}

// For I256. TODO: not ideal
pub(crate) fn get_uniform_i256_die<R: Rng>(
    min_inclusive: I256,
    max_inclusive: I256,
    rng: &mut R,
) -> I256 {
    if min_inclusive == max_inclusive {
        return min_inclusive;
    }

    let range_u256 = if max_inclusive >= min_inclusive {
        let diff = max_inclusive - min_inclusive;
        diff.into_raw()
    } else {
        let pos_part = (I256::MAX - min_inclusive).into_raw();
        let neg_part = (max_inclusive - I256::MIN).into_raw();
        pos_part + neg_part + U256::from(2)
    };

    if range_u256 == U256::MAX {
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        let random_u256 = U256::from_be_bytes(bytes);
        let random_i256 = I256::from_raw(random_u256);
        return random_i256;
    }

    let range_plus_one = range_u256 + U256::from(1);

    loop {
        // Random U256
        let mut bytes = [0u8; 32];
        rng.fill_bytes(&mut bytes);
        let candidate = U256::from_be_bytes(bytes);

        // Rejection sampling
        let multiplier = U256::MAX / range_plus_one;
        let limit = multiplier * range_plus_one;

        if candidate < limit {
            let result = candidate % range_plus_one;
            let result_i256 = I256::from_raw(result);
            return min_inclusive.wrapping_add(result_i256);
        }
    }
}

pub struct U256Uniform {
    min: U256,
    max: U256,
}

impl U256Uniform {
    pub fn new(min: U256, max: U256) -> Self {
        Self { min, max }
    }

    pub fn sample<R: Rng>(&self, rng: &mut R) -> U256 {
        get_uniform_u256_die(self.min, self.max, rng)
    }
}

pub struct I256Uniform {
    min: I256,
    max: I256,
}

impl I256Uniform {
    pub fn new(min: I256, max: I256) -> Self {
        Self { min, max }
    }

    pub fn sample<R: Rng>(&self, rng: &mut R) -> I256 {
        get_uniform_i256_die(self.min, self.max, rng)
    }
}

pub struct QDigitUniform {
    #[cfg(not(target_pointer_width = "64"))]
    inner: Uniform<QDigit>,
    #[cfg(target_pointer_width = "64")]
    inner: U256Uniform,
}

impl QDigitUniform {
    pub fn new(min_inclusive: QDigit, max_inclusive: QDigit) -> Self {
        Self {
            #[cfg(not(target_pointer_width = "64"))]
            inner: get_uniform_die(min_inclusive, max_inclusive),
            #[cfg(target_pointer_width = "64")]
            inner: U256Uniform::new(min_inclusive, max_inclusive),
        }
    }

    pub fn sample<R: Rng>(&self, rng: &mut R) -> QDigit {
        self.inner.sample(rng)
    }
}

pub(crate) fn get_uniform_qdigit_die(
    min_inclusive: QDigit,
    max_inclusive: QDigit,
) -> QDigitUniform {
    QDigitUniform::new(min_inclusive, max_inclusive)
}

pub struct SQDigitUniform {
    #[cfg(not(target_pointer_width = "64"))]
    inner: Uniform<SQDigit>,
    #[cfg(target_pointer_width = "64")]
    inner: I256Uniform,
}

impl SQDigitUniform {
    pub fn new(min_inclusive: SQDigit, max_inclusive: SQDigit) -> Self {
        Self {
            #[cfg(not(target_pointer_width = "64"))]
            inner: get_uniform_die(min_inclusive, max_inclusive),
            #[cfg(target_pointer_width = "64")]
            inner: I256Uniform::new(min_inclusive, max_inclusive),
        }
    }

    pub fn sample<R: Rng>(&self, rng: &mut R) -> SQDigit {
        self.inner.sample(rng)
    }
}

pub(crate) fn get_uniform_sqdigit_die(
    min_inclusive: SQDigit,
    max_inclusive: SQDigit,
) -> SQDigitUniform {
    SQDigitUniform::new(min_inclusive, max_inclusive)
}

/* Comparisons with Arbi */

/* !impl_cmp */
macro_rules! impl_cmp {
    ($($signed:ty => $unsigned:ty),*) => {
        $(

impl CompareWith<$signed> for Arbi {
    fn cmp_with(&self, b: $signed) -> Ordering {
        let a = self;

        // Unsigned integer type with same width as input type for `b`
        type UnsignedT = $unsigned;

        if b == <$signed>::ZERO {
            if a.size() == 0 {
                return Ordering::Equal; // a
            }
            return if a.is_negative() {
                Ordering::Less
            } else {
                Ordering::Greater
            }; // b
        }

        #[allow(unused_comparisons)]
        let b_negative = b < <$signed>::ZERO;
        let unsigned_b: UnsignedT = if b_negative {
            UnsignedT::ZERO.wrapping_sub(UnsignedT::wrapping_from(b))
        } else {
            UnsignedT::wrapping_from(b)
        };

        if a.is_negative() && !b_negative {
            return Ordering::Less; // c
        }
        if !a.is_negative() && b_negative {
            return Ordering::Greater; // d
        }

        let mut n_b_digits: usize = 0;
        if UnsignedT::BITS as u32 <= Digit::BITS {
            n_b_digits = if unsigned_b != UnsignedT::from(0u8) { 1 } else { 0 };
        } else {
            let mut temp_b: UnsignedT = unsigned_b;
            while temp_b != UnsignedT::from(0u8) {
                // temp_b >>= Digit::BITS;
                temp_b = temp_b.shr(Digit::BITS); // For MSRV
                n_b_digits += 1;
            }
        }

        let a_size: usize = a.size();
        if a_size < n_b_digits {
            return if a.is_negative() {
                Ordering::Greater
            } else {
                Ordering::Less
            }; // e
        }

        if a_size > n_b_digits {
            return if a.is_negative() {
                Ordering::Less
            } else {
                Ordering::Greater
            }; // f
        }

        for i in (0..n_b_digits).rev() {
            let a_digit: Digit = a.vec[i];
            let b_digit: Digit =
                ((unsigned_b >> (Digit::BITS as usize * i)) & UnsignedT::from(u64::MAX)).try_into().unwrap();

            if a_digit < b_digit {
                return if a.is_negative() {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }; // g
            }
            if a_digit > b_digit {
                return if a.is_negative() {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }; // h
            }
        }
        Ordering::Equal // i
    }
}

impl PartialEq<$signed> for Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

impl PartialOrd<$signed> for Arbi {
    fn partial_cmp(&self, other: &$signed) -> Option<Ordering> {
        Some(self.cmp_with(*other))
    }
}

impl PartialEq<Arbi> for $signed {
    fn eq(&self, other: &Arbi) -> bool {
        other.cmp_with(*self) == Ordering::Equal
    }
}

impl PartialOrd<Arbi> for $signed {
    fn partial_cmp(&self, other: &Arbi) -> Option<Ordering> {
        Some(other.cmp_with(*self).reverse())
    }
}

impl PartialEq<$signed> for &Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

impl PartialOrd<$signed> for &Arbi {
    fn partial_cmp(&self, other: &$signed) -> Option<Ordering> {
        Some(self.cmp_with(*other))
    }
}

impl PartialEq<$signed> for &mut Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

impl PartialOrd<$signed> for &mut Arbi {
    fn partial_cmp(&self, other: &$signed) -> Option<Ordering> {
        Some(self.cmp_with(*other))
    }
}

        )*
    }
}
/* impl_cmp! */

impl_cmp!(
    U256 => U256,
    I256 => U256
);
