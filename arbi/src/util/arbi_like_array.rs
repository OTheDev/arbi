/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::macros::for_all_ints_with_metadata;
use crate::Digit;
use core::ops::Shr;

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArbiLikeArray<const N: usize> {
    digits: [Digit; N],
    length: usize,
    is_neg: bool,
}

#[allow(dead_code)]
pub(crate) trait IntoArbiLikeArray<const N: usize> {
    fn into_arbi_like_array(self) -> ArbiLikeArray<N>;
}

impl<const N: usize> ArbiLikeArray<N> {
    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn digits(&self) -> &[Digit] {
        &self.digits[..self.length]
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn length(&self) -> usize {
        self.length
    }

    #[allow(dead_code)]
    #[inline(always)]
    pub(crate) fn is_negative(&self) -> bool {
        self.is_neg
    }
}

/* !impl_into_arbi_like_array */
macro_rules! impl_into_arbi_like_array {
    ($(($int:ty, $uint:ty, $max_size:expr)),*) => {
        $(

impl IntoArbiLikeArray<$max_size> for $int {
    #[allow(unused_comparisons)]
    fn into_arbi_like_array(self) -> ArbiLikeArray<$max_size> {
        if self == 0 {
            return ArbiLikeArray {
                digits: [0; $max_size],
                length: 0,
                is_neg: false,
            };
        }
        let is_neg = self < 0;
        let mut value = if is_neg {
            (0 as $uint).wrapping_sub(self as $uint)
        } else {
            self as $uint
        };
        if Digit::BITS >= <$uint>::BITS {
            ArbiLikeArray {
                digits: [value as Digit; $max_size],
                length: 1,
                is_neg,
            }
        } else {
            let mut digits = [0 as Digit; $max_size];
            let mut length = 0;
            while value != 0 {
                digits[length] = (value & (Digit::MAX as $uint)) as Digit;
                // value >>= Digit::BITS;
                value = value.shr(Digit::BITS); // For MSRV
                length += 1;
            }
            ArbiLikeArray {
                digits,
                length,
                is_neg,
            }
        }
    }
}

        )*
    };
}
/* impl_into_arbi_like_array! */

for_all_ints_with_metadata!(impl_into_arbi_like_array);

#[cfg(not(target_pointer_width = "64"))]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero() {
        let x: i32 = 0;
        let stack = x.into_arbi_like_array();
        assert_eq!(stack.length(), 0);
        assert_eq!(stack.is_negative(), false);
        assert!(stack.digits().is_empty());
    }

    #[test]
    fn test_positive() {
        let x: i32 = 42;
        let stack = x.into_arbi_like_array();
        assert_eq!(stack.length(), 1);
        assert_eq!(stack.is_negative(), false);
        assert_eq!(stack.digits(), &[42]);
    }

    #[test]
    fn test_negative() {
        let x: i32 = -42;
        let stack = x.into_arbi_like_array();
        assert_eq!(stack.length(), 1);
        assert_eq!(stack.is_negative(), true);
        assert_eq!(stack.digits(), &[42]);
    }

    #[test]
    fn test_large_unsigned() {
        let x: u64 = 0xFFFF_FFFF_0000_0000;
        let stack = x.into_arbi_like_array();
        assert_eq!(stack.length(), 2);
        assert_eq!(stack.is_negative(), false);
        assert_eq!(stack.digits(), &[0, 0xFFFF_FFFF]);
    }
}

/* !impl_from_int */
macro_rules! impl_from_int {
    ($(($int:ty, $uint:ty, $max_size:expr)),*) => {
        $(

impl From<$int> for ArbiLikeArray<$max_size> {
    fn from(value: $int) -> Self {
        value.into_arbi_like_array()
    }
}

        )*
    };
 }
/* impl_from_int! */

for_all_ints_with_metadata!(impl_from_int);
