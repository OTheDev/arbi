/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::to_digits::{length_digits, ToDigits};
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
    #[inline(always)]
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
    fn dmul_algo_knuth(
        w: &mut [Digit],
        a: &[Digit],
        b: &[Digit],
        m: usize,
        n: usize,
    ) {
        w[..m].fill(0);
        for j in 0..n {
            let mut k: Digit = 0;
            for i in 0..m {
                let t: DDigit = a[i] as DDigit * b[j] as DDigit
                    + w[i + j] as DDigit
                    + k as DDigit;
                k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
                w[i + j] = t as Digit; // t mod 2^{Digit::BITS}
            }
            w[j + m] = k;
        }
    }

    #[allow(dead_code)]
    fn mul_algo_knuth(w: &mut Self, a: &Self, b: &Self, m: usize, n: usize) {
        Arbi::dmul_algo_knuth(&mut w.vec, &a.vec, &b.vec, m, n);
    }

    fn dmul_algo_square(w: &mut [Digit], a: &[Digit], t: usize) {
        use crate::uints::UnsignedUtilities;
        w.fill(0);
        let mut c: DDigit;
        for i in 0..t {
            if Digit::BITS == 32 {
                type QDigit = u128;
                let uv: QDigit =
                    w[2 * i] as QDigit + a[i] as QDigit * a[i] as QDigit;
                w[2 * i] = uv as Digit; // set w[2 * i] <- v
                c = (uv >> Digit::BITS) as DDigit; // set c <- u
                for j in (i + 1)..t {
                    let uv: QDigit = 2 * a[j] as QDigit * a[i] as QDigit
                        + w[i + j] as QDigit
                        + c as QDigit;
                    w[i + j] = uv as Digit; // set w[i + j] <- v
                    c = (uv >> Digit::BITS) as DDigit; // set c <- u
                }
            } else if Digit::BITS == 64 {
                // This works for the 32-bit case as well.
                let uv: DDigit =
                    w[2 * i] as DDigit + a[i] as DDigit * a[i] as DDigit;
                w[2 * i] = uv as Digit; // set w[2 * i] <- v
                c = uv >> Digit::BITS; // set c <- u
                for j in (i + 1)..t {
                    // (hi, lo) represents a quadruple digit
                    let mut lo: DDigit = a[j] as DDigit * a[i] as DDigit;
                    // Multiply product by two
                    let mut hi = lo >> (DDigit::BITS - 1);
                    lo <<= 1;
                    // Now add w[i + j] and c to (hi, lo)
                    let mut lo_clone = lo;
                    let overflow = DDigit::uadd_overflow(
                        &mut lo,
                        lo_clone,
                        w[i + j] as DDigit,
                    );
                    hi += DDigit::from(overflow);
                    lo_clone = lo;
                    let overflow = DDigit::uadd_overflow(&mut lo, lo_clone, c);
                    hi += DDigit::from(overflow);
                    // Collect
                    w[i + j] = lo as Digit; // set w[i + j] <- v
                    c = (hi << Digit::BITS) | (lo >> Digit::BITS); // set c <- u
                }
            } else {
                unreachable!("Digit::BITS must be 32 or 64.");
            }
            let mut k = i + t;
            while c > 0 {
                c += w[k] as DDigit;
                w[k] = c as Digit;
                c >>= Digit::BITS;
                k += 1;
            }
        }
    }

    #[allow(dead_code)]
    fn mul_algo_square(w: &mut Self, a: &Self, t: usize) {
        Arbi::dmul_algo_square(&mut w.vec, &a.vec, t);
    }

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
            Self::dmul_algo_square(&mut result.vec, a, m);
        } else {
            Self::dmul_algo_knuth(&mut result.vec, a, b, m, n);
        }
        result.trim();
    }

    #[allow(dead_code)]
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
        if u.len() < Self::KARATSUBA_THRESHOLD
            || v.len() < Self::KARATSUBA_THRESHOLD
        {
            Self::dmul_standard(w, u, v);
        } else {
            Self::dmul_karatsuba(w, u, v);
        }
        w.neg = u_is_neg != v_is_neg;
    }

    fn mul_(w: &mut Self, u: &Self, v: &Self) {
        Self::dmul_(w, &u.vec, &v.vec, u.is_negative(), v.is_negative());
    }
}

// TODO: any inplace potential?

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl Mul<Arbi> for Arbi {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut ret = Arbi::zero();
        Self::mul_(&mut ret, &self, &rhs);
        ret
    }
}

/// See [`impl<'a, 'b> Mul<&'b Arbi> for &'a Arbi`](#impl-Mul<%26Arbi>-for-%26Arbi).
impl<'a> Mul<&'a Arbi> for Arbi {
    type Output = Self;

    fn mul(self, rhs: &'a Arbi) -> Self {
        let mut ret = Arbi::zero();
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
        let mut ret = Arbi::zero();
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

    use crate::{SDDigit, SDigit};
    // use alloc::string::ToString;
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
        // let distribution = Uniform::new_inclusive(SDDigit::MIN, SDDigit::MAX);
        // for _ in 0..i16::MAX {
        //     let mut a_in: SQDigit = distribution.sample(&mut rng) as SQDigit;
        //     let b_in: SQDigit = distribution.sample(&mut rng) as SQDigit;

        //     let mut a = Arbi::from(a_in);
        //     let b = Arbi::from(b_in);

        //     assert_eq!(&a * &b, a_in * b_in);

        //     a *= &b;
        //     a_in *= b_in;
        //     assert_eq!(a, a_in);
        // }

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

impl Arbi {
    fn dbisect(x: &[Digit], lower: &mut Self, upper: &mut Self, n: usize) {
        let bisect_point = core::cmp::min(n, x.len());
        lower.vec = x[..bisect_point].to_vec();
        upper.vec = x[bisect_point..].to_vec();
        lower.trim();
        upper.trim();
    }

    #[allow(dead_code)]
    fn bisect(x: &Self, lower: &mut Self, upper: &mut Self, n: usize) {
        Self::dbisect(&x.vec, lower, upper, n);
    }

    // TODO: optimize
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

    #[allow(dead_code)]
    fn mul_karatsuba(w: &mut Self, u: &Self, v: &Self) {
        Self::dmul_karatsuba(w, &u.vec, &v.vec);
    }
}

#[cfg(all(feature = "nightly", test))]
mod benches_karatsuba {
    use test::Bencher;

    use super::*;
    use crate::util::test::{
        get_seedable_rng, get_uniform_die, random_arbi, Distribution,
    };

    #[bench]
    fn bench_karatsuba(b: &mut Bencher) {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(
            Arbi::KARATSUBA_THRESHOLD,
            Arbi::KARATSUBA_THRESHOLD * 4,
        );
        b.iter(|| {
            let random_size = Digit::BITS as usize * die.sample(&mut rng);
            let r_1 = random_arbi(random_size);
            let r_2 = random_arbi(random_size);
            let mut x_k = Arbi::zero();
            Arbi::mul_karatsuba(&mut x_k, &r_1, &r_2);
        });
    }

    #[bench]
    fn bench_standard(b: &mut Bencher) {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(
            Arbi::KARATSUBA_THRESHOLD,
            Arbi::KARATSUBA_THRESHOLD * 4,
        );
        b.iter(|| {
            let random_size = Digit::BITS as usize * die.sample(&mut rng);
            let r_1 = random_arbi(random_size);
            let r_2 = random_arbi(random_size);
            let mut x_k = Arbi::zero();
            Arbi::mul_standard(&mut x_k, &r_1, &r_2);
        });
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
    use crate::{SDDigit, SDigit};

    #[test]
    fn test_square_zero() {
        assert_eq!(Arbi::zero() * Arbi::zero(), 0);
    }

    // #[test]
    // fn test_squares_of_digit_boundaries() {
    //     for x in [
    //         SDigit::MIN as SQDigit,
    //         SDigit::MAX as SQDigit,
    //         SDDigit::MIN as SQDigit,
    //         SDDigit::MAX as SQDigit,
    //         Digit::MAX as SQDigit - 1,
    //         Digit::MAX as SQDigit,
    //         Digit::MAX as SQDigit + 1,
    //     ] {
    //         let s = Arbi::from(x);
    //         assert_eq!(
    //             &s * &s,
    //             x * x,
    //             "Square failed with x = {}, arbi = {}",
    //             x,
    //             s,
    //         );
    //     }

    //     let s = Arbi::from(DDigit::MAX);
    //     assert_eq!(&s * &s, DDigit::MAX as QDigit * DDigit::MAX as QDigit)
    // }

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
        // let die_doub = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for i in i16::MIN..i16::MAX {
            let r_sing = die_sing.sample(&mut rng);
            let a_sing = Arbi::from(r_sing);
            assert_eq!(
                &a_sing * &a_sing,
                r_sing as SDDigit * r_sing as SDDigit
            );

            // let r_doub = die_doub.sample(&mut rng);
            // let a_doub = Arbi::from(r_doub);
            // assert_eq!(
            //     &a_doub + &a_doub,
            //     r_doub as SQDigit + r_doub as SQDigit
            // );

            assert_eq!(
                Arbi::from(i) * Arbi::from(i),
                i as SDDigit * i as SDDigit
            );
        }
    }
}

/* !impl_arbi_mul_for_primitive */
macro_rules! impl_arbi_mul_for_primitive {
    ($($signed_type:ty),* ) => {
        $(

impl Mul<$signed_type> for Arbi {
    type Output = Self;
    #[allow(unused_comparisons)]
    fn mul(mut self, other: $signed_type) -> Self {
        match other.to_digits() {
            None => {
                self.make_zero();
                self
            }
            Some(v) => {
                let mut ret = Arbi::zero();
                let v_len: usize = length_digits(&v);
                Self::dmul_(
                    &mut ret,
                    &self.vec,
                    &v[..v_len],
                    self.is_negative(),
                    other < 0,
                );
                ret
            }
        }
    }
}

impl Mul<&$signed_type> for Arbi {
    type Output = Self;
    fn mul(self, other: &$signed_type) -> Self {
        self * (*other)
    }
}

impl Mul<$signed_type> for &Arbi {
    type Output = Arbi;
    fn mul(self, other: $signed_type) -> Arbi {
        self.clone() * other
    }
}

impl Mul<&$signed_type> for &Arbi {
    type Output = Arbi;
    fn mul(self, other: &$signed_type) -> Arbi {
        self.clone() * (*other)
    }
}

impl Mul<Arbi> for $signed_type {
    type Output = Arbi;
    fn mul(self, other: Arbi) -> Arbi {
        other * self
    }
}

impl Mul<&Arbi> for $signed_type {
    type Output = Arbi;
    fn mul(self, other: &Arbi) -> Arbi {
        other.clone() * self
    }
}

impl Mul<Arbi> for &$signed_type {
    type Output = Arbi;
    fn mul(self, other: Arbi) -> Arbi {
        other * (*self)
    }
}

impl Mul<&Arbi> for &$signed_type {
    type Output = Arbi;
    fn mul(self, other: &Arbi) -> Arbi {
        other.clone() * (*self)
    }
}

impl MulAssign<&$signed_type> for Arbi {
    fn mul_assign(&mut self, other: &$signed_type) {
        self.mul_assign(*other);
    }
}

impl MulAssign<$signed_type> for Arbi {
    #[allow(unused_comparisons)]
    fn mul_assign(&mut self, other: $signed_type) {
        match other.to_digits() {
            None => self.make_zero(),
            Some(v) => {
                let self_clone = self.clone();
                let v_len: usize = length_digits(&v);
                Self::dmul_(
                    self,
                    &self_clone.vec,
                    &v[..v_len],
                    self_clone.is_negative(),
                    other < 0,
                );
            }
        }
    }
}

        )*
    }
}
/* impl_arbi_mul_for_primitive! */

impl_arbi_mul_for_primitive![
    i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize
];

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
        // let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            // let lhs = die_sddigit.sample(&mut rng);
            // let mut lhs_arbi = Arbi::from(lhs);
            // let rhs = die_sddigit.sample(&mut rng);
            // let expected = lhs as SQDigit * rhs as SQDigit;
            // assert_eq!(&lhs_arbi * rhs, expected);
            // let mut lhs_clone = lhs_arbi.clone();
            // lhs_clone *= rhs;
            // assert_eq!(lhs_clone, expected);
            // let rhs = die_sdigit.sample(&mut rng);
            // let expected = lhs as SQDigit * rhs as SQDigit;
            // assert_eq!(lhs_arbi.clone() * rhs, expected);
            // lhs_arbi *= rhs;
            // assert_eq!(lhs_arbi, expected);

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            let expected = lhs as SDDigit * rhs as SDDigit;
            assert_eq!(&lhs_arbi * rhs, expected);
            let mut lhs_clone = lhs_arbi.clone();
            lhs_clone *= rhs;
            assert_eq!(lhs_clone, expected);
            // let rhs = die_sddigit.sample(&mut rng);
            // let expected = lhs as SQDigit * rhs as SQDigit;
            // assert_eq!(lhs_arbi.clone() * rhs, expected);
            // lhs_arbi *= rhs;
            // assert_eq!(lhs_arbi, expected);

            // let lhs = die_sddigit.sample(&mut rng);
            // let mut lhs_arbi = Arbi::from(lhs);
            // let rhs = die_sddigit.sample(&mut rng);
            // let expected = rhs as SQDigit * lhs as SQDigit;
            // assert_eq!(rhs * &lhs_arbi, expected);
            // let mut lhs_clone = lhs_arbi.clone();
            // lhs_clone *= rhs;
            // assert_eq!(lhs_clone, expected);
            // let rhs = die_sdigit.sample(&mut rng);
            // let expected = rhs as SQDigit * lhs as SQDigit;
            // assert_eq!(rhs * lhs_arbi.clone(), expected);
            // lhs_arbi *= rhs;
            // assert_eq!(lhs_arbi, expected);

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            let expected = rhs as SDDigit * lhs as SDDigit;
            assert_eq!(rhs * &lhs_arbi, expected);
            let mut lhs_clone = lhs_arbi.clone();
            lhs_clone *= rhs;
            assert_eq!(lhs_clone, expected);
            // let rhs = die_sddigit.sample(&mut rng);
            // let expected = rhs as SQDigit * lhs as SQDigit;
            // assert_eq!(rhs * lhs_arbi.clone(), expected);
            // lhs_arbi *= rhs;
            // assert_eq!(lhs_arbi, expected);
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
