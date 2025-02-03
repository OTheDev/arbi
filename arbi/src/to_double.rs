/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

#[allow(clippy::unnecessary_cast)]
const BASE_DBL: f64 = 2.0 * ((1 as Digit) << (Digit::BITS - 1)) as f64;

impl Arbi {
    /// Convert this integer to a floating-point value.
    ///
    /// The semantics of this function are consistent with [Rust's built-in
    /// behavior for casting from an integer to a float](
    /// https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions).
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Pow};
    ///
    /// let a = Arbi::from(-987654321);
    /// assert_eq!(a.to_f64(), -987654321.0);
    ///
    /// let b = Arbi::from(1_u64 << 32);
    /// assert_ne!((&b).pow(31_usize).to_f64(), f64::INFINITY);
    /// assert_eq!((&b).pow(32_usize).to_f64(), f64::INFINITY);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    pub fn to_f64(&self) -> f64 {
        if self.size() == 0 {
            return 0.0;
        }

        let mut result: f64 = 0.0;

        for (i, j) in (0..self.size()).rev().enumerate() {
            result = result * BASE_DBL + self.vec[j] as f64;
            // result = result.mul_add(BASE_DBL, self.vec[j] as f64);

            if i >= 32 {
                assert!(result.is_infinite());
                break;
            }
        }

        if self.is_negative() {
            -result
        } else {
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use core::f32::NEG_INFINITY;

    use super::*;
    use crate::util::test::float::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, QDigit, SDDigit, SQDigit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_0 = get_uniform_die(MAX_INT_NEG, MAX_INT);
        let die_1 = get_uniform_die(-100.0, 100.0);
        let die_2 = get_uniform_die(DBL_MAX_INT, u64::MAX);
        let die_3 = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        let die_4 = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            let mut random_double: f64;
            let mut int_val: i64;
            let uint_val: u64;
            let qval: SQDigit;
            let sval: SDDigit;

            random_double = die_0.sample(&mut rng);
            int_val = random_double as i64;
            assert_eq!(Arbi::from(random_double).to_f64(), int_val as f64);

            random_double = die_1.sample(&mut rng);
            int_val = random_double as i64;
            assert_eq!(Arbi::from(random_double).to_f64(), int_val as f64);

            uint_val = die_2.sample(&mut rng);
            assert_eq!(Arbi::from(uint_val).to_f64(), uint_val as f64);

            qval = die_3.sample(&mut rng);
            assert_double_eq(Arbi::from(qval).to_f64(), qval as f64);

            sval = die_4.sample(&mut rng);
            assert_double_eq(Arbi::from(sval).to_f64(), sval as f64);
        }
    }

    fn test_db<U>(arb: &Arbi, exp: U)
    where
        U: Into<f64>,
    {
        let arb_as_f64: f64 = arb.to_f64();
        let exp_as_f64: f64 = exp.into();

        assert_eq!(
            arb_as_f64, exp_as_f64,
            "Values are not equal: {} and {}",
            arb_as_f64, exp_as_f64
        );
    }

    #[test]
    fn misc() {
        test_db(&Arbi::from(-1.0), -1.0);
        test_db(&Arbi::from(1.0), 1.0);
        test_db(&Arbi::from(-987654321.0), -987654321.0);
        test_db(&Arbi::from(987654321.0), 987654321.0);
    }

    #[test]
    fn f64_special_values() {
        test_db(&Arbi::from(ZERO), ZERO);
        test_db(&Arbi::from(MAX_INT), MAX_INT);
        test_db(&Arbi::from(MAX_INT_NEG), MAX_INT_NEG);
        test_db(&Arbi::from(MIN_DOUBLE), 0.0);
        test_db(&Arbi::from(LOWEST_DOUBLE), LOWEST_DOUBLE);
        test_db(&Arbi::from(SUBNORMAL_DOUBLE), 0.0);
        test_db(&Arbi::from(MAX_DOUBLE), MAX_DOUBLE);
    }

    #[test]
    fn digit_types_max_and_min() {
        test_db(&Arbi::from(Digit::MAX), Digit::MAX as f64);
        test_db(&Arbi::from(DDigit::MAX), DDigit::MAX as f64);
        test_db(&Arbi::from(QDigit::MAX), QDigit::MAX as f64);
        test_db(&Arbi::from(SQDigit::MIN), SQDigit::MIN as f64);
    }

    #[test]
    fn max_double() {
        let max_double = Arbi::from(MAX_DOUBLE);

        test_db(&max_double, MAX_DOUBLE);
        test_db(&(&max_double + &Arbi::one()), MAX_DOUBLE + 1.0);
        test_db(
            &(&max_double * &Arbi::from(987654321.0)),
            MAX_DOUBLE * 987654321.0,
        );
        test_db(&(&max_double * &max_double), MAX_DOUBLE * MAX_DOUBLE);
        test_db(&(&max_double * &max_double), INF);
        test_db(&(&max_double * &(-&max_double)), NEG_INFINITY);
    }

    #[test]
    fn test_inf() {
        use crate::Pow;

        assert_ne!(
            Arbi::from(BASE_DBL).pow(31_usize).to_f64(),
            // 4.185580496821357e+298
            Arbi::from_str_radix(
                "41855804968213570000000000000000000000000000000000000000000000\
                 00000000000000000000000000000000000000000000000000000000000000\
                 00000000000000000000000000000000000000000000000000000000000000\
                 00000000000000000000000000000000000000000000000000000000000000\
                 000000000000000000000000000000000000000000000000000\
                ", 10).unwrap());
        assert_eq!(Arbi::from(BASE_DBL).pow(32_usize).to_f64(), f64::INFINITY);
    }
}
