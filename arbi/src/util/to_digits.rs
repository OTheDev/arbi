/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/* TODO: Use StackDigits instead. */

use crate::Digit;
use core::ops::Shr;

pub(crate) trait ToDigits<const N: usize> {
    type Output;
    fn to_digits(&self) -> Option<Self::Output>;
}

/* !impl_to_digits_for_primitive */
macro_rules! impl_to_digits_for_primitive {
    ($(($digit_size:expr, $unsigned_type:ty, $signed_type:ty)),* ) => {
        $(

impl ToDigits<$digit_size> for $signed_type {
    type Output = [Digit; $digit_size];
    #[allow(unused_comparisons)]
    fn to_digits(&self) -> Option<Self::Output> {
        if *self == 0 {
            return None;
        }
        let mut value = if *self < 0 {
            (0 as $unsigned_type).wrapping_sub(*self as $unsigned_type)
        } else {
            *self as $unsigned_type
        };
        if Digit::BITS >= <$unsigned_type>::BITS {
            Some([value as Digit; $digit_size])
        } else {
            let mut digits = [0 as Digit; $digit_size];
            for digit in &mut digits {
                *digit = (value & (Digit::MAX as $unsigned_type)) as Digit;
                // value >>= Digit::BITS;
                value = value.shr(Digit::BITS); // For MSRV
            }
            Some(digits)
        }
    }
}

        )*
    }
}
/* impl_to_digits_for_primitive! */

impl_to_digits_for_primitive![
    (1, u8, i8),
    (1, u8, u8),
    (1, u16, i16),
    (1, u16, u16),
    (1, u32, i32),
    (1, u32, u32),
    (2, u64, i64),
    (2, u64, u64),
    (4, u128, i128),
    (4, u128, u128),
    (4, usize, isize),
    (4, usize, usize)
];

/// Return the number of `Digit`s actually needed. Note that this returns `0`
/// if the slice is empty or nonempty with all zeros.
pub(crate) fn length_digits(digits: &[Digit]) -> usize {
    for (index, &digit) in digits.iter().rev().enumerate() {
        if digit != 0 {
            return digits.len() - index;
        }
    }
    0
}

#[cfg(test)]
mod tests {
    use super::length_digits;
    use crate::Digit;

    #[test]
    fn test_length_digits() {
        let a = [Digit::MAX];
        assert_eq!(length_digits(&a), 1);
        let b = [0, 1, 0];
        assert_eq!(length_digits(&b), 2);
        let c = [0, 0, 0];
        assert_eq!(length_digits(&c), 0)
    }
}
