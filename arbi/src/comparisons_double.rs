/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Comparisons with floats.
//! Compare an `Arbi` to a floating-point number.
//!
//! These comparisons are designed to be consistent with IEEE 754, handling
//! special cases like NaNs and infinities.
//!
//! **NaN**:
//! - Operators `==`, `<`, `<=`, `>`, and `>=` return `false` when comparing
//!   with NaN.
//! - Operator `!=` returns `true` when comparing with NaN.
//!
//! **Infinities**:
//! - Positive infinity is treated as greater than any `Arbi` number.
//! - Negative infinity is treated as less than any `Arbi` number.
//!
//! ## Complexity
//! \\( O(1) \\)

use crate::comparisons_integral::CompareWith;
use crate::{Arbi, Digit};
use core::cmp::Ordering;
use core::cmp::{PartialEq, PartialOrd};

#[allow(clippy::unnecessary_cast)]
const BASE_DBL: f64 = 2.0 * ((1 as Digit) << (Digit::BITS - 1)) as f64;
const BASE_DBL_RECIPROCAL: f64 = 1.0 / BASE_DBL;

/*
 *  TRUE: std::ldexp(std::numeric_limits<double>::max(), -1024) < 1  and
 *        std::ldexp(std::numeric_limits<double>::max(), -1023) >= 1
 *  What x makes Digit::BITS * (x - 1) >= 1024?
 *    x >= (1024 / Digit::BITS + 1) := upper [note that 1024 % Digit::BITS == 0]
 *
 *  const upper: usize = 1024 / (Digit::BITS as usize) + 1;
 */
// Floating-point arithmetic in const requires later rust versions.
// const fn find_upper() -> usize {
//     let mut dbl: f64 = f64::MAX;
//     let mut x: usize = 1;
//     while dbl >= 1.0 {
//         dbl *= BASE_DBL_RECIPROCAL;
//         x += 1;
//     }
//     x
// }
// const CMP_DBL_SIZE_UPPER: usize = find_upper();
const CMP_DBL_SIZE_UPPER: usize = 33;

impl Arbi {
    #[allow(dead_code)]
    fn cmp_abs_double(z: &Self, mut dbl: f64) -> Ordering {
        if dbl.is_infinite() {
            if dbl < 0.0 {
                return Ordering::Greater;
            } else {
                return Ordering::Less;
            }
        }
        if z.size() == 0 {
            return if dbl > 0.0 {
                Ordering::Less
            } else {
                Ordering::Equal
            };
        }
        if z.size() >= CMP_DBL_SIZE_UPPER {
            return Ordering::Greater;
        }
        for _ in 1..z.size() {
            // Equiv. to `dbl /= BASE_DBL;`, but multiplication is generally
            // cheaper
            dbl *= BASE_DBL_RECIPROCAL;
        }
        if BASE_DBL <= dbl {
            return Ordering::Less;
        }
        for digit in z.vec.iter().rev() {
            let cur: Digit = dbl as Digit;
            match digit {
                x if *x < cur => {
                    return Ordering::Less;
                }
                x if *x > cur => {
                    return Ordering::Greater;
                }
                _ => {
                    dbl = (dbl - cur as f64) * BASE_DBL;
                }
            }
        }
        if dbl > 0.0 {
            Ordering::Less
        } else {
            Ordering::Equal
        }
    }
}

impl CompareWith<f64> for Arbi {
    fn cmp_with(&self, dbl: f64) -> Ordering {
        if self.is_negative() {
            if dbl < 0.0 {
                match Self::cmp_abs_double(self, -dbl) {
                    Ordering::Less => Ordering::Greater,
                    Ordering::Equal => Ordering::Equal,
                    Ordering::Greater => Ordering::Less,
                }
            } else {
                Ordering::Less
            }
        } else if dbl < 0.0 {
            Ordering::Greater
        } else {
            Self::cmp_abs_double(self, dbl)
        }
    }
}

/// Test if this `Arbi` integer is equal to a floating-point value.
///
/// See also [`PartialOrd<f64> for Arbi`](#impl-PartialOrd<f64>-for-Arbi) for
/// a description of the semantics of comparing an `Arbi` to a floating-point
/// value.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(f64::MAX);
///
/// assert_eq!(a, f64::MAX);
/// assert_ne!(a, f64::MIN);
///
/// // Reverse also implemented
/// assert_eq!(f64::MAX, a);
/// assert_ne!(f64::MIN, a);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialEq<f64> for Arbi {
    fn eq(&self, other: &f64) -> bool {
        !other.is_nan() && (self.cmp_with(*other) == Ordering::Equal)
    }
}

/// Compare this `Arbi` integer to a floating-point value.
///
/// These comparisons are designed to be consistent with IEEE 754, handling
/// special cases like NaNs and infinities.
///
/// **NaN**:
/// - Operators `==`, `<`, `<=`, `>`, and `>=` return `false` when comparing
///   with NaN.
/// - Operator `!=` returns `true` when comparing with NaN.
///
/// **Infinities**:
/// - Positive infinity is treated as greater than any `Arbi` number.
/// - Negative infinity is treated as less than any `Arbi` number.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(987654321.5);
/// assert_eq!(a, 987654321.0);
///
/// assert!(a >= 987654321.0);
/// assert!(a <= 987654321.0);
/// assert!(a > 0.0);
/// assert!(a < u64::MAX);
///
/// // Reverse also implemented
/// assert!(987654321.0 <= a);
/// assert!(987654321.0 >= a);
/// assert!(0.0 < a);
/// assert!(u64::MAX > a);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl PartialOrd<f64> for Arbi {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if !other.is_nan() {
            Some(self.cmp_with(*other))
        } else {
            None
        }
    }
}

/// See [`PartialEq<f64> for Arbi`](#impl-PartialEq<f64>-for-Arbi).
impl PartialEq<f64> for &Arbi {
    fn eq(&self, other: &f64) -> bool {
        !other.is_nan() && ((*self).cmp_with(*other) == Ordering::Equal)
    }
}

/// See [`PartialOrd<f64> for Arbi`](#impl-PartialOrd<f64>-for-Arbi).
impl PartialOrd<f64> for &Arbi {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if !other.is_nan() {
            Some(self.cmp_with(*other))
        } else {
            None
        }
    }
}

/// See [`PartialEq<f64> for Arbi`](#impl-PartialEq<f64>-for-Arbi).
impl PartialEq<Arbi> for f64 {
    fn eq(&self, other: &Arbi) -> bool {
        !self.is_nan() && other.cmp_with(*self) == Ordering::Equal
    }
}

/// See [`PartialOrd<f64> for Arbi`](#impl-PartialOrd<f64>-for-Arbi).
impl PartialOrd<Arbi> for f64 {
    fn partial_cmp(&self, other: &Arbi) -> Option<Ordering> {
        if !self.is_nan() {
            Some(other.cmp_with(*self).reverse())
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::float::*;
    use crate::util::test::{
        get_seedable_rng, get_uniform_die, ldexp, Distribution,
    };
    use crate::{DDigit, SDDigit, SDigit};

    #[test]
    fn compare_to_f64() {
        let zero = Arbi::zero();

        assert_eq!(&zero, ZERO);
        assert!(&zero < MIN_DOUBLE);
        assert!(&zero < SUBNORMAL_DOUBLE);
        assert!(&zero > LOWEST_DOUBLE);

        let max_double = Arbi::from(MAX_DOUBLE);

        // Infinity should be larger than all ints
        assert!(&max_double < INF);
        assert!(zero < INF);

        // -Infinity should be less than all ints
        assert!(-(&max_double) > MINF);
        assert!(zero > MINF);

        let mut max_double_mut = max_double.clone();

        // Boundary around max_double
        assert_eq!(&max_double_mut, MAX_DOUBLE);
        max_double_mut.incr();
        assert!(&max_double_mut > MAX_DOUBLE);
        max_double_mut.decr();
        max_double_mut.decr();
        assert!(&max_double_mut < MAX_DOUBLE);
        assert_eq!(Arbi::from(-MAX_DOUBLE), -MAX_DOUBLE);
        assert!(Arbi::from(-&max_double).incr() > &mut -MAX_DOUBLE);
        assert!(Arbi::from(-&max_double).decr() < &mut -MAX_DOUBLE);

        /* IEEE 754: NaN compared to another floating point number x (where x
         * can be finite, an infinite, or NaN) evaluates to false with >=, <=,
         * >, <, ==, but true when NaN != x is evaluated. */
        let one = Arbi::one();
        assert!(&one != NAN);
        assert!(!(&one == NAN));
        assert!(!(&one < NAN));
        assert!(!(&one <= NAN));
        assert!(!(&one >= NAN));
        assert!(!(&one > NAN));

        // BASE_DBL <= dbl (comparisons with infinities above also trigger this)
        assert!(Arbi::from(DDigit::MAX) <= DDigit::MAX as f64);

        // Misc.
        assert!(Arbi::from(SDDigit::MIN) >= SDDigit::MIN as f64);
        assert!(Arbi::from(SDigit::MIN) >= SDigit::MIN as f64);
        assert!(Arbi::from(Digit::MAX) <= Digit::MAX as f64);

        // *x < cur; one iteration (max_double ones above cover > 1 iteration)
        assert!(
            (Arbi::one() << Digit::BITS as usize)
                < ldexp(1.0, Digit::BITS as i32 + 1)
        );
        assert!(
            (Arbi::one() << (Digit::BITS * 2) as usize)
                < ldexp(1.0, (Digit::BITS as i32) * 2 + 1)
        );

        // *x > cur; one iteration (max_double ones above cover > 1 iteration)
        assert!(
            (Arbi::one() << (Digit::BITS + 2) as usize)
                > ldexp(1.0, Digit::BITS as i32 + 1)
        );
        assert!(
            (Arbi::one() << (Digit::BITS * 2 + 2) as usize)
                > ldexp(1.0, Digit::BITS as i32 * 2 + 1)
        );

        // z.size() >= CMP_DBL_SIZE_UPPER. The `large` variable is the first
        // number possible that will trigger this condition of the impl.
        let shift = Digit::BITS as usize * (CMP_DBL_SIZE_UPPER - 1);
        let large = Arbi::one() << shift; // First number possible
        if Digit::BITS == 32 {
            assert_eq!(large.size(), 33);
        }
        assert!(&large > f64::MAX);
        assert!((&large + &Arbi::one()) > f64::MAX);
        assert!((&large - &Arbi::one()) > f64::MAX); // does not trigger cond.
    }

    #[test]
    fn misc() {
        assert!(Arbi::from(5) > 4.9);
        assert!(4.9 < Arbi::from(5));
        assert!(Arbi::one() > -1.0);
        assert!(Arbi::neg_one() < 1.0);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(MAX_INT_NEG, MAX_INT);
        for _ in 0..i16::MAX {
            let rand_double: f64 = die.sample(&mut rng);
            let int64: i64 = rand_double as i64;
            let rand_arbi = Arbi::from(rand_double);

            assert_eq!(rand_arbi, int64);

            if rand_double < 0.0 {
                assert!(rand_arbi >= rand_double);
            } else {
                assert!(rand_arbi <= rand_double);
            }
        }
    }
}
