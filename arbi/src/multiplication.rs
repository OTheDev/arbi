/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, DDigit, Digit};
use core::ops::{Mul, MulAssign};

impl Arbi {
    #[allow(dead_code)]
    /// If one of the operands has size greater than or equal to this value,
    /// then we use Karatsuba multiplication.
    const KARATSUBA_THRESHOLD: usize = 74;

    /// Multiply this integer in place by a digit and optionally, add a digit
    /// to this integer.
    ///
    /// This function does not trim trailing zeros in the digit vector.
    ///
    /// Knuth Algorithm M, but recognizing
    /// 1. \\( j \\) is always 0
    /// 2. \\( w\_{i + j} = w\_{i} \\) is always zero when forming \\( t \\).
    /// 3. We can safely make the initial carry nonzero to implement adding a
    ///    digit.
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    #[allow(dead_code)]
    pub(crate) fn imul1add1(x: &mut Self, v: Digit, k: Option<Digit>) {
        let mut k: Digit = k.unwrap_or(0);
        for d in &mut x.vec {
            let t: DDigit = (*d as DDigit) * (v as DDigit) + (k as DDigit);
            k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
            *d = t as Digit; // t mod 2^{Digit::BITS}
        }

        if k != 0 {
            x.vec.push(k);
        }
    }

    /// Grade School Multiplication Algorithm
    fn mul_algo_knuth(w: &mut Self, a: &Self, b: &Self, m: usize, n: usize) {
        w.vec[..m].fill(0);

        for j in 0..n {
            let mut k: Digit = 0;
            for i in 0..m {
                let t: DDigit = a.vec[i] as DDigit * b.vec[j] as DDigit
                    + w.vec[i + j] as DDigit
                    + k as DDigit;
                k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
                w.vec[i + j] = t as Digit; // t mod 2^{Digit::BITS}
            }
            w.vec[j + m] = k;
        }
    }

    fn mul_algo_square(w: &mut Self, a: &Self, t: usize) {
        use crate::{uints::UnsignedUtilities, QDigit};

        w.vec.fill(0);

        let mut c: DDigit;
        for i in 0..t {
            if Digit::BITS == 32 {
                let uv: QDigit = w.vec[2 * i] as QDigit
                    + a.vec[i] as QDigit * a.vec[i] as QDigit;
                w.vec[2 * i] = uv as Digit; // set w[2 * i] <- v
                c = (uv >> Digit::BITS) as DDigit; // set c <- u

                for j in (i + 1)..t {
                    let uv: QDigit =
                        2 * a.vec[j] as QDigit * a.vec[i] as QDigit
                            + w.vec[i + j] as QDigit
                            + c as QDigit;
                    w.vec[i + j] = uv as Digit; // set w[i + j] <- v
                    c = (uv >> Digit::BITS) as DDigit; // set c <- u
                }
            } else if Digit::BITS == 64 {
                // This works for the 32-bit case as well.
                let uv: DDigit = w.vec[2 * i] as DDigit
                    + a.vec[i] as DDigit * a.vec[i] as DDigit;
                w.vec[2 * i] = uv as Digit; // set w[2 * i] <- v
                c = uv >> Digit::BITS; // set c <- u

                for j in (i + 1)..t {
                    // (hi, lo) represents a quadruple digit
                    let mut lo: DDigit =
                        a.vec[j] as DDigit * a.vec[i] as DDigit;

                    // Multiply product by two
                    let mut hi = lo >> (DDigit::BITS - 1);
                    lo <<= 1;

                    // Now add w[i + j] and c to (hi, lo)
                    let mut lo_clone = lo;
                    let overflow = DDigit::uadd_overflow(
                        &mut lo,
                        lo_clone,
                        w.vec[i + j] as DDigit,
                    );
                    hi += if overflow { 1 } else { 0 };
                    lo_clone = lo;
                    let overflow = DDigit::uadd_overflow(&mut lo, lo_clone, c);
                    hi += if overflow { 1 } else { 0 };

                    w.vec[i + j] = lo as Digit; // set w[i + j] <- v
                    c = (hi << Digit::BITS) | (lo >> Digit::BITS); // set c <- u
                }
            } else {
                unreachable!("Digit::BITS must be 32 or 64.");
            }

            let mut k = i + t;
            while c > 0 {
                c += w.vec[k] as DDigit;
                w.vec[k] = c as Digit;
                c >>= Digit::BITS;
                k += 1;
            }
        }
    }

    // Performs `result = |a| * |b|`.
    fn mul_standard(result: &mut Self, a: &Self, b: &Self) {
        if a.size() == 0 || b.size() == 0 {
            result.make_zero();
            return;
        }

        let m = a.size();
        let n = b.size();
        result.vec.resize(m + n, 0);

        if core::ptr::eq(a, b) {
            Self::mul_algo_square(result, a, m);
        } else {
            Self::mul_algo_knuth(result, a, b, m, n);
        }

        result.trim();
    }

    fn mul_(w: &mut Self, u: &Self, v: &Self) {
        if u.size() < Self::KARATSUBA_THRESHOLD
            || v.size() < Self::KARATSUBA_THRESHOLD
        {
            Self::mul_standard(w, u, v);
        } else {
            Self::mul_karatsuba(w, u, v);
        }
        w.neg = u.is_negative() != v.is_negative();
    }
}

// TODO: any inplace potential?

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl Mul<Arbi> for Arbi {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut ret = Arbi::default();
        Self::mul_(&mut ret, &self, &rhs);
        ret
    }
}

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl<'a> Mul<&'a Arbi> for Arbi {
    type Output = Self;

    fn mul(self, rhs: &'a Arbi) -> Self {
        let mut ret = Arbi::default();
        Self::mul_(&mut ret, &self, rhs);
        ret
    }
}

/// Multiply an `Arbi` integer by another `Arbi` integer.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let mut a = Arbi::from(i16::MIN);
/// let mut b = a.clone();
///
/// a = &a * &b;
/// assert_eq!(a, (i16::MIN as i128).pow(2));
///
/// a = a * &b;
/// assert_eq!(a, (i16::MIN as i128).pow(3));
///
/// a *= &b;
/// assert_eq!(a, (i16::MIN as i128).pow(4));
///
/// a *= b;
/// assert_eq!(a, (i16::MIN as i128).pow(5));
///
/// a = &a * &a;
/// assert_eq!(
///     a,
///     Arbi::from_str_radix("40000000000000000000000000000000000000", 16)
///         .unwrap()
/// );
/// ```
///
/// ## Complexity
/// \\( O(n^{\log\_{2}(3)}) \approx O(n^{1.58}) \\)
impl<'b> Mul<&'b Arbi> for &Arbi {
    type Output = Arbi;

    fn mul(self, rhs: &'b Arbi) -> Self::Output {
        let mut ret = Arbi::default();
        Arbi::mul_(&mut ret, self, rhs);
        ret
    }
}

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl MulAssign<Arbi> for Arbi {
    fn mul_assign(&mut self, rhs: Arbi) {
        *self = &*self * &rhs;
    }
}

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl MulAssign<&Arbi> for Arbi {
    fn mul_assign(&mut self, rhs: &Arbi) {
        *self = &*self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{SDDigit, SDigit, SQDigit};
    use alloc::string::ToString;
    use rand::distributions::Distribution;
    use rand::distributions::Uniform;

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
            let mut a_in: SQDigit = distribution.sample(&mut rng) as SQDigit;
            let b_in: SQDigit = distribution.sample(&mut rng) as SQDigit;

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

        let mut a = Arbi::from(DDigit::MAX);
        a *= Arbi::from(SDDigit::MIN);
        assert_eq!(a.to_string(), "-170141183460469231722463931679029329920");
    }

    // Can't do a *= &a.
    #[test]
    fn test_mult_assign_self_multiplication() {
        let mut a = Arbi::from(7);
        a *= a.clone();
        assert_eq!(a, 49);

        let mut a = Arbi::from(DDigit::MAX);
        a *= a.clone();
        assert_eq!(a.to_string(), "340282366920938463426481119284349108225");

        let mut a = Arbi::from(SDDigit::MIN);
        a *= a.clone();
        assert_eq!(a.to_string(), "85070591730234615865843651857942052864");
    }
}

impl Arbi {
    fn bisect(x: &Self, lower: &mut Self, upper: &mut Self, n: usize) {
        let bisect_point = core::cmp::min(n, x.size());

        lower.vec = x.vec[..bisect_point].to_vec();
        upper.vec = x.vec[bisect_point..].to_vec();

        lower.trim();
        upper.trim();
    }

    fn mul_karatsuba(w: &mut Self, u: &Self, v: &Self) {
        let n: usize = core::cmp::min(u.size(), v.size()) >> 1;

        let (mut u0, mut u1, mut v0, mut v1) =
            (Arbi::zero(), Arbi::zero(), Arbi::zero(), Arbi::zero());
        Self::bisect(u, &mut u0, &mut u1, n);
        Self::bisect(v, &mut v0, &mut v1, n);

        let (mut a, mut b, mut c) = (Arbi::zero(), Arbi::zero(), Arbi::zero());
        Self::mul_(&mut a, &u1, &v1); // a = u1 * v1
        Self::mul_(&mut b, &u0, &v0); // b = u0 * v0

        u1 += u0;
        v1 += v0;
        Self::mul_(&mut c, &u1, &v1);
        c -= &a + &b; // c = (u1 + u0)(v1 + v0) - (u0v0 + u1v1)

        a <<= 2 * n * Digit::BITS as usize;
        c <<= n * Digit::BITS as usize;
        *w = &a + &c + &b; // w = (Arbi::BASE ** 2n) * a + (Arbi::BASE ** n) * c + b
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
        let die = get_uniform_die(
            Arbi::KARATSUBA_THRESHOLD,
            Arbi::KARATSUBA_THRESHOLD * 4,
        );

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

            assert_eq!(x_karatsuba, x_standard);
        }
    }
}

#[cfg(test)]
mod square {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{QDigit, SDDigit, SDigit, SQDigit};

    #[test]
    fn test_square_zero() {
        assert_eq!(Arbi::zero() * Arbi::zero(), 0);
    }

    #[test]
    fn test_squares_of_digit_boundaries() {
        for x in [
            SDigit::MIN as SQDigit,
            SDigit::MAX as SQDigit,
            SDDigit::MIN as SQDigit,
            SDDigit::MAX as SQDigit,
            Digit::MAX as SQDigit - 1,
            Digit::MAX as SQDigit,
            Digit::MAX as SQDigit + 1,
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
        assert_eq!(&s * &s, DDigit::MAX as QDigit * DDigit::MAX as QDigit)
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
                r_doub as SQDigit + r_doub as SQDigit
            );

            assert_eq!(
                Arbi::from(i) * Arbi::from(i),
                i as SDDigit * i as SDDigit
            );
        }
    }
}
