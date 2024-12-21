/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Comparisons with integral types
//!
//! Efficient comparison between `Arbi`s and any standard integral type, with no
//! implicit conversions from integral values to `Arbi`s (and hence no memory
//! allocation).

use crate::{Arbi, Digit};
use core::cmp::Ordering;
use core::ops::Shr;

pub(crate) trait CompareWith<T> {
    fn cmp_with(&self, other: T) -> Ordering;
}

/* !impl_cmp */
macro_rules! impl_cmp {
    ($($signed:ty => $unsigned:ty),*) => {
        $(

impl CompareWith<$signed> for Arbi {
    fn cmp_with(&self, b: $signed) -> Ordering {
        let a = self;

        // Unsigned integer type with same width as input type for `b`
        type UnsignedT = $unsigned;

        if b == 0 {
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
        let b_negative = b < 0;
        let unsigned_b: UnsignedT = if b_negative {
            (0 as UnsignedT).wrapping_sub(b as UnsignedT)
        } else {
            b as UnsignedT
        };

        if a.is_negative() && !b_negative {
            return Ordering::Less; // c
        }
        if !a.is_negative() && b_negative {
            return Ordering::Greater; // d
        }

        let mut n_b_digits: usize = 0;
        if UnsignedT::BITS <= Digit::BITS {
            n_b_digits = if unsigned_b != 0 { 1 } else { 0 };
        } else {
            let mut temp_b: UnsignedT = unsigned_b;
            while temp_b != 0 {
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
                (unsigned_b >> (Digit::BITS as usize * i)) as Digit;

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

/// Test if this `Arbi` integer is equal to a primitive integer value.
///
/// This is implemented for all primitive integer types.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(u64::MAX);
/// assert_eq!(a, u64::MAX);
/// assert_ne!(a, u64::MAX - 1);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialEq<$signed> for Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

/// Compare the value of this `Arbi` integer to a primitive integer value.
///
/// This is implemented for all primitive integer types.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(u64::MAX);
/// assert!(a > 0);
/// assert!(a < u128::MAX);
/// assert!(a >= 0);
/// assert!(a <= u128::MAX);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialOrd<$signed> for Arbi {
    fn partial_cmp(&self, other: &$signed) -> Option<Ordering> {
        Some(self.cmp_with(*other))
    }
}

/// Test if this primitive integer value is equal to an `Arbi` integer.
///
/// This is implemented for all primitive integer types.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(u64::MAX);
/// assert_eq!(u64::MAX, a);
/// assert_ne!(u64::MAX - 1, a);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialEq<Arbi> for $signed {
    fn eq(&self, other: &Arbi) -> bool {
        other.cmp_with(*self) == Ordering::Equal
    }
}

/// Compare the value of this primitive integer value to an `Arbi` integer.
///
/// This is implemented for all primitive integer types.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(u64::MAX);
/// assert!(0 < a);
/// assert!(u128::MAX > a);
/// assert!(0 <= a);
/// assert!(u128::MAX >= a);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialOrd<Arbi> for $signed {
    fn partial_cmp(&self, other: &Arbi) -> Option<Ordering> {
        Some(other.cmp_with(*self).reverse())
    }
}

/// See [`PartialEq<i32> for Arbi`](#impl-PartialEq<i32>-for-Arbi).
impl PartialEq<$signed> for &Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

/// See [`PartialOrd<i32> for Arbi`](#impl-PartialOrd<i32>-for-Arbi).
impl PartialOrd<$signed> for &Arbi {
    fn partial_cmp(&self, other: &$signed) -> Option<Ordering> {
        Some(self.cmp_with(*other))
    }
}

/// See [`PartialEq<i32> for Arbi`](#impl-PartialEq<i32>-for-Arbi).
impl PartialEq<$signed> for &mut Arbi {
    fn eq(&self, other: &$signed) -> bool {
        self.cmp_with(*other) == Ordering::Equal
    }
}

/// See [`PartialOrd<i32> for Arbi`](#impl-PartialOrd<i32>-for-Arbi).
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
mod test_compare_with_integral {
    use super::*;
    use crate::{DDigit, SDDigit};

    fn setup() -> (Arbi, Arbi, Arbi, Arbi, Arbi) {
        let zero = Arbi::zero();
        let positive = Arbi::from(123456789);
        let negative = Arbi::from(-987654321);
        let tdigit = Arbi::from(Digit::MAX as DDigit + 242092);
        let tdigit_n = Arbi::from(-(Digit::MAX as SDDigit + 242092));

        (zero, positive, negative, tdigit, tdigit_n)
    }

    #[test]
    fn test_cmp() {
        let (zero, positive, negative, tdigit, tdigit_n) = setup();

        // a
        assert!(zero == 0);

        // b
        assert!(positive > 0);
        assert!(negative < 0);

        // c
        assert!(Arbi::from(-500) < 1409209);

        // d
        assert!(zero > -1409209);
        assert!(positive > -1409209);

        // e
        assert!(0 < 32902);
        assert!(Arbi::from(42920) < (Digit::MAX as DDigit + 2920));
        assert!(Arbi::from(-42920) > -(Digit::MAX as SDDigit + 2920));

        // f
        assert!(tdigit > 3293);
        assert!(tdigit_n < -42092);

        // g
        assert!(tdigit < (Digit::MAX as DDigit + 342093));
        assert!(tdigit_n > -(Digit::MAX as SDDigit + 342093));

        // h
        assert!(tdigit > (Digit::MAX as DDigit + 2920));
        assert!(tdigit_n < (-(Digit::MAX as SDDigit + 2920)));

        // i
        assert!(Arbi::from(Digit::MAX) == Digit::MAX);
        assert!(
            Arbi::from(-(Digit::MAX as SDDigit)) == -(Digit::MAX as SDDigit)
        );
        assert!(Arbi::from(SDDigit::MIN) == SDDigit::MIN);
        assert!(Arbi::from(DDigit::MAX) == DDigit::MAX);
    }

    #[test]
    fn test_cmp_reversed() {
        let (zero, positive, negative, tdigit, tdigit_n) = setup();

        // a
        assert!(0 == zero);

        // b
        assert!(0 < positive);
        assert!(0 > negative);

        // c
        assert!(1409209 > Arbi::from(-500));

        // d
        assert!(-1409209 < zero);
        assert!(-1409209 < positive);

        // e
        assert!(32902 > Arbi::new());
        assert!(Digit::MAX as DDigit + 2920 > Arbi::from(42920));
        assert!(-(Digit::MAX as SDDigit + 2920) < Arbi::from(-42920));

        // f
        assert!(3293 < tdigit);
        assert!(-42092 > tdigit_n);

        // g
        assert!(Digit::MAX as DDigit + 342093 > tdigit);
        assert!(-(Digit::MAX as SDDigit + 342093) < tdigit_n);

        // h
        assert!(Digit::MAX as DDigit + 2920 < tdigit);
        assert!(-(Digit::MAX as SDDigit + 2920) > tdigit_n);

        // i
        assert!(Digit::MAX == Arbi::from(Digit::MAX));
        assert!(
            -(Digit::MAX as SDDigit) == Arbi::from(-(Digit::MAX as SDDigit))
        );
        assert!(SDDigit::MIN == Arbi::from(SDDigit::MIN));
        assert!(DDigit::MAX == Arbi::from(DDigit::MAX));
    }
}
