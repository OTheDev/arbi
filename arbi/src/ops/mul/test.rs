/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/* TODO: clean up, and move what we can to integration tests */

use crate::ops::mul::impls::s_mul_gradeschool;
use crate::ops::mul::square::s_square;
use crate::ops::mul::MUL_KARATSUBA_CUTOFF;
use crate::{Arbi, Digit};

impl Arbi {
    // Performs `result = |a| * |b|`.
    fn dmul_standard(result: &mut Self, a: &[Digit], b: &[Digit]) {
        let m = a.len();
        let n = b.len();
        if m == 0 || n == 0 {
            result.make_zero();
            return;
        }
        result.vec.resize(m + n, 0);
        if core::ptr::eq(a, b) {
            s_square(&mut result.vec, a, &mut []);
        } else {
            if m >= n {
                s_mul_gradeschool(&mut result.vec, a, b);
            } else {
                s_mul_gradeschool(&mut result.vec, b, a);
            }
        }
        result.trim();
    }

    // Performs `result = |a| * |b|`.
    fn mul_standard(result: &mut Self, a: &Self, b: &Self) {
        Arbi::dmul_standard(result, &a.vec, &b.vec);
    }

    fn dmul_(
        w: &mut Self,
        u: &[Digit],
        v: &[Digit],
        u_is_neg: bool,
        v_is_neg: bool,
    ) {
        if u.len() < MUL_KARATSUBA_CUTOFF || v.len() < MUL_KARATSUBA_CUTOFF {
            Self::dmul_standard(w, u, v);
        } else {
            Self::dmul_karatsuba(w, u, v);
        }
        w.neg = u_is_neg != v_is_neg;
    }

    fn dbisect(x: &[Digit], lower: &mut Self, upper: &mut Self, n: usize) {
        let bisect_point = core::cmp::min(n, x.len());
        lower.vec = x[..bisect_point].to_vec();
        upper.vec = x[bisect_point..].to_vec();
        lower.trim();
        upper.trim();
    }

    fn dmul_karatsuba(w: &mut Self, u: &[Digit], v: &[Digit]) {
        let n: usize = core::cmp::min(u.len(), v.len()) >> 1;
        let (mut u0, mut u1, mut v0, mut v1) =
            (Arbi::zero(), Arbi::zero(), Arbi::zero(), Arbi::zero());
        Self::dbisect(u, &mut u0, &mut u1, n);
        Self::dbisect(v, &mut v0, &mut v1, n);
        let (mut a, mut b, mut c) = (Arbi::zero(), Arbi::zero(), Arbi::zero());
        Self::dmul_(
            &mut a,
            &u1.vec,
            &v1.vec,
            u1.is_negative(),
            v1.is_negative(),
        ); // a = u1 * v1
        Self::dmul_(
            &mut b,
            &u0.vec,
            &v0.vec,
            u0.is_negative(),
            v0.is_negative(),
        ); // b = u0 * v0
        u1 += u0;
        v1 += v0;
        Self::dmul_(
            &mut c,
            &u1.vec,
            &v1.vec,
            u1.is_negative(),
            v1.is_negative(),
        );
        // c -= &a + &b; // c = (u1 + u0)(v1 + v0) - (u0v0 + u1v1)
        c.sub_sum_of_abs_gt(&a, &b);
        a <<= 2 * n * Digit::BITS as usize;
        c <<= n * Digit::BITS as usize;
        // *w = &a + &c + &b; // w = (Arbi::BASE ** 2n) * a + (Arbi::BASE ** n) * c + b
        w.add3_abs_assign(&a, &b, &c);
    }

    fn mul_karatsuba(w: &mut Self, u: &Self, v: &Self) {
        Self::dmul_karatsuba(w, &u.vec, &v.vec);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{DDigit, SDDigit, SDigit};
    // use alloc::string::ToString;
    use crate::SQDigit;
    use rand::distributions::Distribution;
    use rand::distributions::Uniform;

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn test_mul_misc() {
        let a = Arbi::from(DDigit::MAX);
        let b = a.clone();

        assert_eq!(
            (&a * &b).to_string_base(10.try_into().unwrap()),
            "340282366920938463426481119284349108225"
        );

        let b = Arbi::from(SDDigit::MIN);

        assert_eq!(
            (&a * &b).to_string_base(10.try_into().unwrap()),
            "-170141183460469231722463931679029329920"
        );
    }

    #[test]
    fn test_mul() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let zero = Arbi::new();

        assert_eq!(&a * &b, -50);
        assert_eq!(&b * &a, -50);
        assert_eq!(&a * &zero, 0);
        assert_eq!(&a * &a, 100);
        assert_eq!(&b * &b, 25);

        // Very small
        for i in i8::MIN..i8::MAX {
            for j in i8::MIN..i8::MAX {
                let mut a = Arbi::from(i);
                let b = Arbi::from(j);
                let expected = i as i32 * j as i32;

                assert_eq!(&a * &b, expected);

                a *= &b;
                assert_eq!(a, expected);
            }
        }

        let mut rng = rand::thread_rng();

        let die = Uniform::new_inclusive(Digit::MIN, Digit::MAX);
        for _ in 0..i16::MAX {
            let rval = die.sample(&mut rng);
            let arbi = Arbi::from(rval);

            let mask = Arbi::from(Digit::MAX);
            assert_eq!(&arbi * &mask, rval as DDigit * Digit::MAX as DDigit);

            let maskp2 = Arbi::from(Digit::MAX as DDigit + 2);
            assert_eq!(
                &arbi * &maskp2,
                rval as DDigit * (Digit::MAX as DDigit + 2)
            );
        }

        let die_s = Uniform::new_inclusive(SDigit::MIN, SDigit::MAX);
        for _ in 0..i16::MAX {
            let rval: SDigit = die_s.sample(&mut rng);
            let r = Arbi::from(rval);
            let mask = Arbi::from(Digit::MAX);
            assert_eq!(r * mask, rval as SDDigit * Digit::MAX as SDDigit);
        }

        // Large, multi-digit
        let distribution = Uniform::new_inclusive(SDDigit::MIN, SDDigit::MAX);
        for _ in 0..i16::MAX {
            let mut a_in: SQDigit =
                SQDigit::try_from(distribution.sample(&mut rng)).unwrap();
            let b_in: SQDigit =
                SQDigit::try_from(distribution.sample(&mut rng)).unwrap();

            let mut a = Arbi::from(a_in);
            let b = Arbi::from(b_in);

            assert_eq!(&a * &b, a_in * b_in);

            a *= &b;
            a_in *= b_in;
            assert_eq!(a, a_in);
        }

        // Small, single-digit
        let dist_small = Uniform::new_inclusive(SDigit::MIN, SDigit::MAX);
        for _ in 0..i16::MAX {
            let mut a_in: SDDigit = dist_small.sample(&mut rng) as SDDigit;
            let b_in: SDDigit = dist_small.sample(&mut rng) as SDDigit;

            let mut a = Arbi::from(a_in);
            let b = Arbi::from(b_in);

            assert_eq!(&a * &b, a_in * b_in);

            a *= &b;
            a_in *= b_in;
            assert_eq!(a, a_in);
        }
    }

    #[test]
    fn test_mult_assign() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);
        a *= &b;
        assert_eq!(a, -50);

        #[cfg(not(target_pointer_width = "64"))]
        {
            let mut a = Arbi::from(DDigit::MAX);
            a *= Arbi::from(SDDigit::MIN);
            assert_eq!(
                a.to_string(),
                "-170141183460469231722463931679029329920"
            );
        }
    }

    // Can't do a *= &a.
    #[test]
    fn test_mult_assign_self_multiplication() {
        let mut a = Arbi::from(7);
        a *= a.clone();
        assert_eq!(a, 49);

        #[cfg(not(target_pointer_width = "64"))]
        {
            let mut a = Arbi::from(DDigit::MAX);
            a *= a.clone();
            assert_eq!(
                a.to_string(),
                "340282366920938463426481119284349108225"
            );

            let mut a = Arbi::from(SDDigit::MIN);
            a *= a.clone();
            assert_eq!(a.to_string(), "85070591730234615865843651857942052864");
        }
    }
}

#[cfg(test)]
mod karatsuba {
    use super::*;
    use crate::util::test::{
        get_seedable_rng, get_uniform_die, random_arbi, Distribution,
    };

    #[test]
    fn test_karatsuba() {
        let (mut rng, _) = get_seedable_rng();
        let die =
            get_uniform_die(MUL_KARATSUBA_CUTOFF * 3, MUL_KARATSUBA_CUTOFF * 3);

        let num_iterations = 1000;

        for _ in 0..num_iterations {
            let (mut x_k, mut x_n) = (Arbi::zero(), Arbi::zero());
            let r_1 = random_arbi(Digit::BITS as usize * die.sample(&mut rng));
            let r_2 = random_arbi(Digit::BITS as usize * die.sample(&mut rng));

            Arbi::mul_karatsuba(&mut x_k, &r_1, &r_2);
            Arbi::mul_standard(&mut x_n, &r_1, &r_2);

            assert_eq!(x_k, x_n);
        }

        let bernoulli = get_uniform_die(0, 1);
        for _ in 0..num_iterations {
            let mut r_1 =
                random_arbi(Digit::BITS as usize * die.sample(&mut rng));
            let mut r_2 =
                random_arbi(Digit::BITS as usize * die.sample(&mut rng));

            if r_1.size() == 0 || r_2.size() == 0 {
                continue;
            }

            // Negate at random
            if bernoulli.sample(&mut rng) != 0 {
                r_1.negate_mut();
            }
            if bernoulli.sample(&mut rng) != 0 {
                r_2.negate_mut();
            }

            let is_result_negative = r_1.is_negative() != r_2.is_negative();

            let x_karatsuba = &r_1 * &r_2;
            let mut x_standard = Arbi::zero();
            Arbi::mul_standard(&mut x_standard, &r_1, &r_2);
            if is_result_negative {
                x_standard.negate_mut();
            }

            assert_eq!(x_karatsuba, x_standard, "Test failed with {r_1} * {r_2}, right is correct, left is wrong");
        }
    }
}

#[cfg(test)]
mod square {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, QDigit, SDDigit, SDigit, SQDigit};

    #[test]
    fn test_square_zero() {
        assert_eq!(Arbi::zero() * Arbi::zero(), 0);
    }

    #[test]
    fn test_squares_of_digit_boundaries() {
        for x in [
            SQDigit::try_from(SDigit::MIN).unwrap(),
            SQDigit::try_from(SDigit::MAX).unwrap(),
            SQDigit::try_from(SDDigit::MIN).unwrap(),
            SQDigit::try_from(SDDigit::MAX).unwrap(),
            SQDigit::try_from(Digit::MAX).unwrap()
                - SQDigit::try_from(1).unwrap(),
            SQDigit::try_from(Digit::MAX).unwrap(),
            SQDigit::try_from(Digit::MAX).unwrap()
                + SQDigit::try_from(1).unwrap(),
        ] {
            let s = Arbi::from(x);
            assert_eq!(
                &s * &s,
                x * x,
                "Square failed with x = {}, arbi = {}",
                x,
                s,
            );
        }

        let s = Arbi::from(DDigit::MAX);
        assert_eq!(
            &s * &s,
            QDigit::from(DDigit::MAX) * QDigit::from(DDigit::MAX)
        );
    }

    #[test]
    fn test_squares_misc() {
        let c = &[
            ("174440041", "30429327904081681"),
            ("3657500101", "13377306988815010201"),
            ("88362852307", "7807993667828695222249"),
            ("414507281407", "171816286339421887899649"),
            ("2428095424619", "5895647391055721911295161"),
            ("4952019383323", "24522495972806705210522329"),
            ("12055296811267", "145330181207744298218145289"),
            ("17461204521323", "304893663335470777561670329"),
            ("28871271685163", "833550328718494773794336569"),
            ("53982894593057", "2914152908645102685632605249"),
            ("340282366920938463463374607431768211456",
             "115792089237316195423570985008687907853269984665640564039457584007913129639936"),
            ("340282366920938463463374607431768211457",
             "115792089237316195423570985008687907853950549399482440966384333222776666062849"),
            ("57896044618658097711785492504343953926634992332820282019728792003956564819968",
             "3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412251521024")
        ];

        for x in c {
            let p = Arbi::from_str_base(x.0, 10.try_into().unwrap()).unwrap();
            let expected =
                Arbi::from_str_base(x.1, 10.try_into().unwrap()).unwrap();
            assert_eq!(&p * &p, expected);
        }
    }

    #[test]
    fn test_square_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sing = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_doub = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for i in i16::MIN..i16::MAX {
            let r_sing = die_sing.sample(&mut rng);
            let a_sing = Arbi::from(r_sing);
            assert_eq!(
                &a_sing * &a_sing,
                r_sing as SDDigit * r_sing as SDDigit
            );

            let r_doub = die_doub.sample(&mut rng);
            let a_doub = Arbi::from(r_doub);
            assert_eq!(
                &a_doub + &a_doub,
                SQDigit::try_from(r_doub).unwrap()
                    + SQDigit::try_from(r_doub).unwrap()
            );

            assert_eq!(
                Arbi::from(i) * Arbi::from(i),
                i as SDDigit * i as SDDigit
            );
        }
    }
}

#[cfg(test)]
mod test_mul_with_integral {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{SDDigit, SDigit};

    #[test]
    fn test_mul_zero() {
        let mut a = Arbi::zero();
        assert_eq!(&a * 0, 0);
        a = Arbi::from(123456789);
        assert_eq!(a * 0, 0);

        let mut a = Arbi::zero();
        assert_eq!(0 * &a, 0);
        a = Arbi::from(123456789);
        assert_eq!(0 * a, 0);
    }

    #[test]
    fn test_mul_with_digit_or_less() {
        let mut a = Arbi::from(-932011);
        let rhs = 1216627769_i64;
        assert_eq!(&a * rhs, -1133910463613459_i64);
        a = Arbi::from(-rhs);
        assert_eq!(a * rhs, -1480183128301917361i128);

        let mut a = Arbi::from(-932011);
        let rhs = -1216627769;
        assert_eq!(rhs * &a, 1133910463613459i64);
        a = Arbi::from(rhs);
        assert_eq!(rhs * a, 1480183128301917361i128);
    }

    #[test]
    fn test_mul_with_more_than_a_digit() {
        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = -138125232528959610630283137756024i128;
        assert_eq!(&a * rhs, expected);
        assert_eq!(a * rhs, expected);

        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = -138125232528959610630283137756024i128;
        assert_eq!(rhs * &a, expected);
        assert_eq!(rhs * a, expected);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        #[cfg(not(target_pointer_width = "64"))]
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            #[cfg(not(target_pointer_width = "64"))]
            {
                let lhs = die_sddigit.sample(&mut rng);
                let mut lhs_arbi = Arbi::from(lhs);
                let rhs = die_sddigit.sample(&mut rng);
                let expected = lhs as SQDigit * rhs as SQDigit;
                assert_eq!(&lhs_arbi * rhs, expected);
                let mut lhs_clone = lhs_arbi.clone();
                lhs_clone *= rhs;
                assert_eq!(lhs_clone, expected);
                let rhs = die_sdigit.sample(&mut rng);
                let expected = lhs as SQDigit * rhs as SQDigit;
                assert_eq!(lhs_arbi.clone() * rhs, expected);
                lhs_arbi *= rhs;
                assert_eq!(lhs_arbi, expected);
            }

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            let expected = lhs as SDDigit * rhs as SDDigit;
            assert_eq!(&lhs_arbi * rhs, expected);
            let mut lhs_clone = lhs_arbi.clone();
            lhs_clone *= rhs;
            assert_eq!(lhs_clone, expected);
            #[cfg(not(target_pointer_width = "64"))]
            {
                let rhs = die_sddigit.sample(&mut rng);
                let expected = lhs as SQDigit * rhs as SQDigit;
                assert_eq!(lhs_arbi.clone() * rhs, expected);
                lhs_arbi *= rhs;
                assert_eq!(lhs_arbi, expected);
            }

            #[cfg(not(target_pointer_width = "64"))]
            {
                let lhs = die_sddigit.sample(&mut rng);
                let mut lhs_arbi = Arbi::from(lhs);
                let rhs = die_sddigit.sample(&mut rng);
                let expected = rhs as SQDigit * lhs as SQDigit;
                assert_eq!(rhs * &lhs_arbi, expected);
                let mut lhs_clone = lhs_arbi.clone();
                lhs_clone *= rhs;
                assert_eq!(lhs_clone, expected);
                let rhs = die_sdigit.sample(&mut rng);
                let expected = rhs as SQDigit * lhs as SQDigit;
                assert_eq!(rhs * lhs_arbi.clone(), expected);
                lhs_arbi *= rhs;
                assert_eq!(lhs_arbi, expected);
            }

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            let expected = rhs as SDDigit * lhs as SDDigit;
            assert_eq!(rhs * &lhs_arbi, expected);
            let mut lhs_clone = lhs_arbi.clone();
            lhs_clone *= rhs;
            assert_eq!(lhs_clone, expected);
            #[cfg(not(target_pointer_width = "64"))]
            {
                let rhs = die_sddigit.sample(&mut rng);
                let expected = rhs as SQDigit * lhs as SQDigit;
                assert_eq!(rhs * lhs_arbi.clone(), expected);
                lhs_arbi *= rhs;
                assert_eq!(lhs_arbi, expected);
            }
        }
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn smoke_3_to_4_digits() {
        let (mut rng, _) = get_seedable_rng();
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            let lhs = die_sqdigit.sample(&mut rng);
            let mut lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_mul(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(&lhs_arbi * rhs, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_mul(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(lhs_arbi.clone() * rhs, expected);
            lhs_arbi *= rhs;
            assert_eq!(lhs_arbi, expected);

            let lhs = die_sqdigit.sample(&mut rng);
            let mut lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (rhs as SQDigit).checked_mul(lhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs * &lhs_arbi, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (rhs as SQDigit).checked_mul(lhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs * lhs_arbi.clone(), expected);
            lhs_arbi *= rhs;
            assert_eq!(lhs_arbi, expected);
        }
    }
}
