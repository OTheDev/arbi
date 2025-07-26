/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::assign::Assign;
use crate::{Arbi, Digit};
use core::ops::Shr;

/* !impl_assign_from_primitive */
macro_rules! impl_assign_from_primitive {
    ($(($signed:ty, $unsigned:ty)),*) => {
        $(

impl Assign<$signed> for Arbi {
    /// Assign a builtin integral type value to an `Arbi`.
    fn assign(&mut self, value: $signed) {
        type UnsignedT = $unsigned;

        let mut uvalue: UnsignedT = match value {
            0 => {
                self.neg = false;
                self.vec.clear();
                return;
            }
            #[allow(unused_comparisons)]
            x if x < 0 => {
                self.neg = true;
                (0 as UnsignedT).wrapping_sub(value as UnsignedT)
            }
            _ => {
                self.neg = false;
                value as UnsignedT
            }
        };

        if <$signed>::BITS <= Digit::BITS {
            self.vec.resize(1, 0);
            self.vec[0] = uvalue as Digit;
        } else {
            let mut temp: UnsignedT = uvalue;
            let mut n_digits: usize = 1;
            loop {
                // temp >>= Digit::BITS;
                temp = temp.shr(Digit::BITS); // For MSRV
                if temp == 0 {
                    break;
                }
                n_digits += 1;
            }

            self.vec.resize(n_digits, 0);
            let mut i: usize = 0;
            while uvalue != 0 {
                self.vec[i] = uvalue as Digit;
                // uvalue >>= Digit::BITS;
                uvalue = uvalue.shr(Digit::BITS); // For MSRV
                i += 1;
            }
        }
    }
}

impl Assign<&$signed> for Arbi {
    /// Assign a builtin integral type value to an `Arbi`.
    fn assign(&mut self, value: &$signed) {
        self.assign(*value)
    }
}

        )*
    };
}
/* impl_assign_from_primitive! */

impl_assign_from_primitive!(
    (i8, u8),
    (i16, u16),
    (i32, u32),
    (i64, u64),
    (i128, u128),
    (isize, usize),
    (u8, u8),
    (u16, u16),
    (u32, u32),
    (u64, u64),
    (u128, u128),
    (usize, usize)
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DDigit;

    #[test]
    fn test_assign_from_primitive() {
        let mut arbi = Arbi::new();

        arbi.assign(i8::MIN);
        assert_eq!(arbi, i8::MIN);
        arbi.assign(i8::MAX);
        assert_eq!(arbi, i8::MAX);

        arbi.assign(i16::MIN);
        assert_eq!(arbi, i16::MIN);
        arbi.assign(i16::MAX);
        assert_eq!(arbi, i16::MAX);

        arbi.assign(i32::MIN);
        assert_eq!(arbi, i32::MIN);
        arbi.assign(i32::MAX);
        assert_eq!(arbi, i32::MAX);

        arbi.assign(i64::MIN);
        assert_eq!(arbi, i64::MIN);
        arbi.assign(i64::MAX);
        assert_eq!(arbi, i64::MAX);

        arbi.assign(i128::MIN);
        assert_eq!(arbi, i128::MIN);
        arbi.assign(i128::MAX);
        assert_eq!(arbi, i128::MAX);

        arbi.assign(isize::MIN);
        assert_eq!(arbi, isize::MIN);
        arbi.assign(isize::MAX);
        assert_eq!(arbi, isize::MAX);

        arbi.assign(u8::MAX);
        assert_eq!(arbi, u8::MAX);

        arbi.assign(u16::MAX);
        assert_eq!(arbi, u16::MAX);

        arbi.assign(u32::MAX);
        assert_eq!(arbi, u32::MAX);

        arbi.assign(u64::MAX);
        assert_eq!(arbi, u64::MAX);

        arbi.assign(u128::MAX);
        assert_eq!(arbi, u128::MAX);

        arbi.assign(usize::MAX);
        assert_eq!(arbi, usize::MAX);

        arbi.assign(0);
        assert_eq!(arbi, 0);
    }

    #[test]
    fn test_assign_from_primitive_digit_boundaries() {
        let mut arbi = Arbi::new();

        arbi.assign(Digit::MAX - 1);
        assert_eq!(arbi, Digit::MAX - 1);
        arbi.assign(Digit::MAX);
        assert_eq!(arbi, Digit::MAX);
        arbi.assign(Digit::MAX as DDigit + 1);
        assert_eq!(arbi, Digit::MAX as DDigit + 1);

        arbi.assign(DDigit::MAX - 1);
        assert_eq!(arbi, DDigit::MAX - 1);
        arbi.assign(DDigit::MAX);
        assert_eq!(arbi, DDigit::MAX);
        // arbi.assign(DDigit::MAX as QDigit + 1);
        // assert_eq!(arbi, DDigit::MAX as QDigit + 1);
    }
}

#[cfg(test)]
mod translation_tests {
    use super::*;
    use alloc::string::ToString;

    fn test_integer_value<T>(value: T, expected_str: &str)
    where
        T: Into<Arbi> + Clone + core::fmt::Display + 'static,
        Arbi: Assign<T>,
    {
        let mut x: Arbi = value.clone().into();
        assert_eq!(x.to_string(), expected_str, "Failed for type: {}", value);

        <Arbi as Assign<T>>::assign(&mut x, value.clone());
        assert_eq!(x.to_string(), expected_str);

        let mut y: Arbi = Arbi::new();
        <Arbi as Assign<T>>::assign(&mut y, value.clone());
        assert_eq!(y.to_string(), expected_str);
    }

    fn test_integer<T>()
    where
        T: Into<Arbi>
            + Clone
            + core::fmt::Display
            + core::cmp::PartialEq
            + MinMax
            + 'static,
        Arbi: Assign<T>,
    {
        let min = T::min_value();
        let max = T::max_value();

        test_integer_value(min.clone(), &min.to_string());
        test_integer_value(max.clone(), &max.to_string());
    }

    #[test]
    fn test_integral_types() {
        test_integer::<i8>();
        test_integer::<i16>();
        test_integer::<i32>();
        test_integer::<i64>();
        test_integer::<i128>();
        test_integer::<isize>();

        test_integer::<u8>();
        test_integer::<u16>();
        test_integer::<u32>();
        test_integer::<u64>();
        test_integer::<u128>();
        test_integer::<usize>();
    }

    trait MinMax {
        fn min_value() -> Self;
        fn max_value() -> Self;
    }

    /* !impl_min_max_for_primitive */
    macro_rules! impl_min_max_for_primitive {
        ($($t:ty),*) => {
            $(

    impl MinMax for $t {
        fn min_value() -> Self {
            <$t>::MIN
        }

        fn max_value() -> Self {
            <$t>::MAX
        }
    }

            )*
        };
    }
    /* impl_min_max_for_primitive! */

    impl_min_max_for_primitive!(
        i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
    );
}
