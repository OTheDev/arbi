/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! From C++20 (7.3.10, p. 93): "A prvalue of a floating-point type can be
//! converted to a prvalue of an integer type. The conversion truncates; that
//! is, the fractional part is discarded. The behavior is undefined if the
//! truncated value cannot be represented in the destination type."
//!
//! <https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions>
//! Casting from a float to an integer will round the float towards zero.
//! - `NaN` will return `0`
//! - Values larger than the maximum integer value, including `INFINITY`, will
//!   saturate to the maximum value of the integer type.
//! - Values smaller than the minimum integer value, including `NEG_INFINITY`,
//!   will saturate to the minimum value of the integer type.

use crate::assign::Assign;
use crate::{Arbi, Digit};

#[allow(clippy::unnecessary_cast)]
const BASE_DBL: f64 = 2.0 * ((1 as Digit) << (Digit::BITS - 1)) as f64;
const BASE_DBL_RECIPROCAL: f64 = 1.0 / BASE_DBL;

impl Assign<f64> for Arbi {
    /// Assign a floating-point value to an `Arbi`.
    ///
    /// ## Panic
    /// Panics when attempting to convert a `NaN` or infinity.
    ///
    /// ## Note
    /// In Rust, when casting a primitive float to a primitive integer type,
    /// `NaN`s  are converted to `0` and values with large magnitudes and
    /// infinities are saturated to the maximum and minimum values of the
    /// integer type.
    ///
    /// In contrast, this function panics in these scenarios.
    fn assign(&mut self, d: f64) {
        let mut d = d;

        if d.is_nan() || d.is_infinite() {
            panic!(
                "Conversion error: NaN or infinity cannot be converted to an \
                 integer."
            );
        }

        if d > -1.0 && d < 1.0 {
            self.assign(0);
            return;
        }

        let neg: bool = d < 0.0;
        if neg {
            d = -d;
        }

        let mut n_digits: usize = 1;
        while BASE_DBL <= d {
            // Equiv. to `d /= BASE_DBL;`, but multiplication is generally
            // cheaper.
            d *= BASE_DBL_RECIPROCAL;
            n_digits += 1;
        }

        self.vec.resize(n_digits, 0);

        for i in (0..n_digits).rev() {
            self.vec[i] = d as Digit;
            d = (d - self.vec[i] as f64) * BASE_DBL;
        }

        self.neg = neg;
        self.trim();
    }
}

impl Assign<&f64> for Arbi {
    /// Assign a floating-point value to an `Arbi`.
    ///
    /// ## Panic
    /// Panics when attempting to convert a `NaN` or infinity.
    ///
    /// ## Note
    /// In Rust, when casting a primitive float to a primitive integer type,
    /// `NaN`s  are converted to `0` and values with large magnitudes and
    /// infinities are saturated to the maximum and minimum values of the
    /// integer type.
    ///
    /// In contrast, this function panics in these scenarios.
    fn assign(&mut self, d: &f64) {
        self.assign(*d)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::BASE10;

    fn test_doub<T>(value: f64, exp: T)
    where
        T: PartialEq + core::fmt::Debug,
        Arbi: PartialEq<T>,
    {
        // Test construct from
        assert_eq!(Arbi::from(value), exp, "{:?} != {:?}", value, exp);

        // Test assign from
        let mut x = Arbi::new();
        x.assign(value);
        assert_eq!(x, exp, "{:?} != {:?}", value, exp);
    }

    #[test]
    fn test_f64_zero() {
        test_doub(0.0, 0.0);
        test_doub(-0.0, 0.0);
    }

    #[test]
    fn test_f64_min_positive() {
        test_doub(f64::MIN_POSITIVE, 0.0);
    }

    #[test]
    fn test_f64_min() {
        test_doub(f64::MIN, f64::MIN);
    }

    #[test]
    fn test_f64_max() {
        test_doub(f64::MAX, f64::MAX);
    }

    #[test]
    #[should_panic]
    fn test_f64_nan() {
        test_doub(f64::NAN, 0.0);
    }

    #[test]
    #[should_panic]
    fn test_f64_infinity() {
        test_doub(f64::INFINITY, 0.0);
    }

    #[test]
    #[should_panic]
    fn test_f64_neg_infinity() {
        test_doub(f64::NEG_INFINITY, 0.0);
    }

    #[test]
    fn test_f64_subnormal() {
        use crate::util::test::float::SUBNORMAL_DOUBLE;
        test_doub(SUBNORMAL_DOUBLE, 0.0);
    }

    #[test]
    fn test_f64_max_int() {
        test_doub(
            9007199254740992.0,
            Arbi::from_str_base("9007199254740992", BASE10).unwrap(),
        );
    }

    #[test]
    fn test_f64_max_int_neg() {
        test_doub(
            -9007199254740992.0,
            Arbi::from_str_base("-9007199254740992", BASE10).unwrap(),
        );
    }

    #[test]
    fn test_misc() {
        test_doub(9876.54321, 9876);
        test_doub(-9876.54321, -9876);
        test_doub(0.987654321, 0);
        test_doub(0.999999999, 0);
        test_doub(-0.999999999, 0);
        test_doub(1e-109, 0);
        test_doub(
            1e109,
            Arbi::from_str_base(
                "9999999999999999818508707188399807864717650964328171247958398\
                 369899072554380053298205803424393137676263358464",
                BASE10,
            )
            .unwrap(),
        );
    }

    #[test]
    fn smoke() {
        use crate::util::test::float::{MAX_INT, MAX_INT_NEG};
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };

        let (mut rng, _) = get_seedable_rng();
        let die_0 = get_uniform_die(MAX_INT_NEG, MAX_INT);
        let die_1 = get_uniform_die(-100.0, 100.0);

        for _ in 0..i16::MAX {
            let mut random_double: f64;
            let mut int_val: i64;

            random_double = die_0.sample(&mut rng);
            int_val = random_double as i64;
            test_doub(random_double, int_val as f64);

            random_double = die_1.sample(&mut rng);
            int_val = random_double as i64;
            test_doub(random_double, int_val as f64);
        }
    }
}
