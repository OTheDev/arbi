/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! <https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions>
//! Casting from a smaller integer to a larger integer (e.g. u8 -> u32) will
//! - zero-extend if the source is unsigned
//! - sign-extend if the source is signed

use crate::{Arbi, Digit};

/* !impl_from_integral */
macro_rules! impl_from_integral {
    ($($signed:ty => $unsigned:ty),*) => {
        $(

/// Construct an `Arbi` integer from this primitive integer type value.
///
/// This is implemented for all primitive integer types.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(u128::MAX);
/// assert_eq!(a, u128::MAX);
///
/// let b = Arbi::from(i128::MIN);
/// assert_eq!(b, i128::MIN);
///
/// // Also works with references
/// let c = Arbi::from(&i128::MIN);
/// assert_eq!(c, i128::MIN);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
#[allow(unused_comparisons)]
impl From<$signed> for Arbi {
    fn from(value: $signed) -> Self {
        type UnsignedT = $unsigned;

        let mut uvalue: UnsignedT;
        let mut x = Arbi::default();
        if value == 0 {
            return x;
        } else if value < 0 {
            uvalue = (0 as UnsignedT).wrapping_sub(value as UnsignedT);
            x.neg = true;
        } else {
            uvalue = value as UnsignedT;
            x.neg = false;
        }

        if UnsignedT::BITS <= Digit::BITS {
            x.vec.resize(1, 0);
            x.vec[0] = uvalue as Digit;
            return x;
        }
        let mut size = 1;
        let mut temp: UnsignedT = uvalue;

        loop {
            temp >>= Digit::BITS;
            if temp == 0 {
                break;
            }
            size += 1;
        }

        x.vec.resize(size, 0);

        // Or just loop from 0..size
        let mut i = 0;
        while uvalue != 0 {
            x.vec[i] = uvalue as Digit;
            uvalue >>= Digit::BITS;
            i += 1;
        }

        x
    }
}

/// Construct an `Arbi` integer from this primitive integer type value.
///
/// See [`impl From<i32> for Arbi`](#impl-From<i32>-for-Arbi).
impl From<&$signed> for Arbi {
    fn from(value: &$signed) -> Self {
        Arbi::from(*value)
    }
}

        )*
    }
}
/* impl_from_integral! */

impl_from_integral!(
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

#[cfg(test)]
mod test_internal_representation_after_from_integral {
    use super::*;
    use crate::{DDigit, QDigit, SDDigit};
    use alloc::string::ToString;

    #[test]
    fn test_digit_max() {
        let digit_max: Arbi = Digit::MAX.into();

        assert_eq!(digit_max.vec.len(), 1);
        assert_eq!(digit_max.vec[0], Digit::MAX);
        assert_eq!(digit_max.neg, false);
    }

    #[test]
    fn test_digit_max_plus_one() {
        let digit_max: Arbi = (Digit::MAX as DDigit + 1).into();

        assert_eq!(digit_max.vec.len(), 2);
        assert_eq!(digit_max.vec[0], 0);
        assert_eq!(digit_max.vec[1], 1);
        assert_eq!(digit_max.neg, false);
    }

    #[test]
    fn test_minus_digit_max() {
        let minus_digit_max: Arbi = (-(Digit::MAX as i128)).into();

        assert_eq!(minus_digit_max.vec.len(), 1);
        assert_eq!(minus_digit_max.vec[0], Digit::MAX);
        assert_eq!(minus_digit_max.neg, true);
    }

    #[test]
    fn test_minus_digit_max_plus_one() {
        let minus_digit_max: Arbi = (-(Digit::MAX as SDDigit + 1)).into();

        assert_eq!(minus_digit_max.vec.len(), 2);
        assert_eq!(minus_digit_max.vec[0], 0);
        assert_eq!(minus_digit_max.vec[1], 1);
        assert_eq!(minus_digit_max.neg, true);
    }

    #[test]
    fn test_ddigit_max() {
        let ddigit_max = Arbi::from(DDigit::MAX);
        assert_eq!(ddigit_max, DDigit::MAX);
    }

    #[test]
    fn test_construct_from_integrals() {
        // Small unsigned
        for i in 1 as Digit..u16::MAX as Digit {
            let a = Arbi::from(i);

            assert_eq!(a.size(), 1);
            assert_eq!(a.vec[0], i);
            assert_eq!(a.to_string(), i.to_string());
            assert_eq!(a, i);
        }

        // DDigit
        for i in 0 as Digit..u16::MAX as Digit {
            let a = Arbi::from(DDigit::MAX - i as DDigit);
            assert_eq!(a.size(), 2);
            assert_eq!(a.vec[0], Digit::MAX - i);
            assert_eq!(a.vec[1], Digit::MAX);
            assert_eq!(a.to_string(), (DDigit::MAX - i as DDigit).to_string());
            assert_eq!(a, DDigit::MAX - i as DDigit);
        }

        // QDigit
        for i in 0 as Digit..u16::MAX as Digit {
            let a = Arbi::from(QDigit::MAX - i as QDigit);
            assert_eq!(a.size(), 4);
            assert_eq!(a.vec[0], Digit::MAX - i);
            assert_eq!(a.vec[1], Digit::MAX);
            assert_eq!(a.vec[2], Digit::MAX);
            assert_eq!(a.vec[3], Digit::MAX);
            assert_eq!(a.to_string(), (QDigit::MAX - i as QDigit).to_string());
            assert_eq!(a, QDigit::MAX - i as QDigit);
        }

        // Signed ints, small absolute value
        for i in i16::MIN..0 {
            let a = Arbi::from(i);
            assert_eq!(a.negative(), true);
            assert_eq!(a.size(), 1);
            assert_eq!(a.vec[0], i.unsigned_abs() as Digit);
            assert_eq!(a.to_string(), i.to_string());
            assert_eq!(a, i);
        }
        for i in 1..i16::MAX {
            let a = Arbi::from(i);
            assert_eq!(a.negative(), false);
            assert_eq!(a.size(), 1);
            assert_eq!(a.vec[0], i as Digit);
            assert_eq!(a.to_string(), i.to_string());
            assert_eq!(a, i);
        }

        // Signed its, large absolute value
        for i in 0..u16::MAX {
            let a = Arbi::from(SDDigit::MAX - i as SDDigit);
            assert_eq!(a.negative(), false);
            assert_eq!(a.size(), 2);
            assert_eq!(a.vec[0], Digit::MAX - i as Digit);
            assert_eq!(
                a.vec[1],
                ((1 as Digit) << (Digit::BITS - 1)) - 1 as Digit
            );
            assert_eq!(
                a.to_string(),
                (SDDigit::MAX - i as SDDigit).to_string()
            );
            assert_eq!(a, SDDigit::MAX - i as SDDigit);
        }
        for i in 0..u16::MAX {
            let a = Arbi::from(SDDigit::MIN + i as SDDigit);
            assert_eq!(a.negative(), true);
            assert_eq!(a.size(), 2);

            if i == 0 {
                assert_eq!(a.vec[0], i as Digit);
                assert_eq!(a.vec[1], (1 as Digit) << (Digit::BITS - 1));
            } else {
                assert_eq!(a.vec[0], Digit::MAX - i as Digit + 1);
                assert_eq!(
                    a.vec[1],
                    ((1 as Digit) << (Digit::BITS - 1)) - 1 as Digit
                );
            }
            assert_eq!(
                a.to_string(),
                (SDDigit::MIN + i as SDDigit).to_string()
            );
            assert_eq!(a, SDDigit::MIN + i as SDDigit);
        }
    }
}
