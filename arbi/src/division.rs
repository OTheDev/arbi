/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::to_digits::{length_digits, ToDigits};
use crate::util::ArbiLikeView;
use crate::{Arbi, BitCount, DDigit, Digit, SDDigit};
use core::ops::{Div, DivAssign, Rem, RemAssign};

impl Arbi {
    fn ddiv_algo_single(q: &mut Self, r: &mut Self, u: &[Digit], v: &[Digit]) {
        let mut rem: DDigit = 0;
        for j in (0..u.len()).rev() {
            let temp: DDigit = (rem << Digit::BITS) | u[j] as DDigit; // rem * Arbi::BASE + u[j]
            q.vec[j] = (temp / v[0] as DDigit) as Digit;
            rem = temp % v[0] as DDigit;
        }
        r.vec[0] = rem as Digit;
        q.trim();
        r.trim();
    }

    #[allow(dead_code)]
    fn div_algo_single(q: &mut Self, r: &mut Self, u: &Self, v: &Self) {
        Self::ddiv_algo_single(q, r, &u.vec, &v.vec);
    }

    /// NOTE: Assumes space and size have already been set for q and r.
    #[allow(dead_code)]
    fn div_algo_digit(q: &mut Self, u: &Self, v: Digit) -> Digit {
        let mut rem: DDigit = 0;
        for j in (0..u.vec.len()).rev() {
            let temp: DDigit = (rem << Digit::BITS) | u.vec[j] as DDigit; // rem * Arbi::BASE + u[j]
            q.vec[j] = (temp / v as DDigit) as Digit;
            rem = temp % v as DDigit;
        }
        q.trim();
        rem as Digit
    }

    pub(crate) fn div_algo_digit_inplace(q: &mut Self, v: Digit) -> Digit {
        let mut rem: DDigit = 0;
        for j in (0..q.vec.len()).rev() {
            let temp: DDigit = (rem << Digit::BITS) | q.vec[j] as DDigit; // rem * Arbi::BASE + u[j]
            q.vec[j] = (temp / v as DDigit) as Digit;
            rem = temp % v as DDigit;
        }
        q.trim();
        rem as Digit
    }

    /// In div_algo_binary(), (1) should already have been accounted for and
    /// space (no need for size, but it's okay if it's been set) should already
    /// have been allocated for q, r. Moreover, unlike some multiple-precision
    /// division algorithms, this algorithm works for v.size() == 1 too.
    #[allow(dead_code)]
    fn div_algo_binary(q: &mut Self, r: &mut Self, u: &Self, v: &Self) {
        // (2)
        q.make_zero();
        r.make_zero();
        // (3)
        #[allow(clippy::unnecessary_cast)]
        for i in ((0 as BitCount)..u.size_bits()).rev() {
            // (3)(I)
            *r <<= 1_usize;
            // (3)(II)
            if u.test_bit(i) {
                #[allow(clippy::unnecessary_cast)]
                r.set_bit(0 as BitCount);
            }
            // (3)(III)
            if Arbi::cmp_abs(r, v) != core::cmp::Ordering::Less {
                // (3)(III)(a)
                // *r = &(*r) - v;
                r.isub_with_arbi_like_view(v.into()); // previously, Arbi::sub_abs_inplace(r, v, false); r = |r| - |v|
                                                      // (3)(III)(b)
                q.set_bit(i);
            }
        }
    }

    fn ddiv_algo_knuth(q: &mut Self, r: &mut Self, u: &[Digit], v: &[Digit]) {
        let m = u.len();
        let n = v.len();

        const BASE: DDigit = Digit::MAX as DDigit + 1;
        const B_HALF: Digit = (BASE >> 1) as Digit;

        /* (1) Normalize */
        // Find e such that b > 2^{e} * v_{n-1} >= b / 2
        let v_msd: Digit = v[n - 1];
        let mut e: u32 = 0;
        while (v_msd << e) < B_HALF {
            e += 1;
        }

        let compl_e: u32 = Digit::BITS - e;

        let mut u_norm = Arbi::zero();
        let mut v_norm = Arbi::zero();
        u_norm.vec.resize(m + 1, 0);
        v_norm.vec.resize(n, 0);

        // u_norm set to u * 2^{e}. Cast to ddigit as e may be 0 which would be
        // UB
        u_norm.vec[0] = u[0] << e;
        for i in 1..m {
            u_norm.vec[i] = (((u[i] as DDigit) << e)
                | (u[i - 1] as DDigit >> compl_e as DDigit))
                as Digit;
        }
        u_norm.vec[m] = (u[m - 1] as DDigit >> compl_e) as Digit;

        // v_norm set to v * 2^{e}
        v_norm.vec[0] = v[0] << e;
        for i in 1..n {
            v_norm.vec[i] = (((v[i] as DDigit) << e)
                | (v[i - 1] as DDigit >> compl_e as DDigit))
                as Digit;
        }

        let vp: Digit = v_norm.vec[n - 1];
        let vpp: Digit = v_norm.vec[n - 2];

        /* (2) Initialize j. Also (7) Loop on j */
        for j in (0..(m - n + 1)).rev() {
            /* (3) Calculate q_hat */
            let tmp: DDigit = u_norm.vec[j + n] as DDigit * BASE
                + u_norm.vec[j + n - 1] as DDigit;
            let mut q_hat: DDigit = tmp / vp as DDigit;
            let mut r_hat: DDigit = tmp % vp as DDigit;

            while q_hat == BASE
                || q_hat * vpp as DDigit
                    > BASE * r_hat + u_norm.vec[j + n - 2] as DDigit
            {
                q_hat -= 1;
                r_hat += vp as DDigit;
                if r_hat >= BASE {
                    break;
                }
            }

            /* (4) Multiply and subtract */
            let mut b: SDDigit = 0;
            for i in 0..n {
                let product: DDigit = q_hat * v_norm.vec[i] as DDigit;
                let stmp: SDDigit = u_norm.vec[j + i] as SDDigit
                    - (product as Digit) as SDDigit
                    - b;
                u_norm.vec[j + i] = stmp as Digit;
                b = (product >> Digit::BITS) as SDDigit - (stmp >> Digit::BITS);
            }
            let neg = (u_norm.vec[j + n] as SDDigit) < b;
            u_norm.vec[j + n] = (u_norm.vec[j + n] as SDDigit - b) as Digit;

            /* (5) Test remainder */
            q.vec[j] = q_hat as Digit;

            if neg {
                /* (6) Add back */
                // Decrease q_{j} by 1
                q.vec[j] -= 1;

                // Add (0v_{n-1}...v_{0})_{b} to (u_{j+n}...u_{j})_{b}
                let mut c: Digit = 0;
                for i in 0..n {
                    let tmp: DDigit = (u_norm.vec[j + i] as DDigit
                        + v_norm.vec[i] as DDigit)
                        + c as DDigit;
                    u_norm.vec[j + i] = tmp as Digit;
                    c = (tmp >> Digit::BITS) as Digit;
                }

                // A carry will occur to the left of u_{j+n} and it should be
                // ignored.
                u_norm.vec[j + n] = (u_norm.vec[j + n]).wrapping_add(c);
                assert_eq!(u_norm.vec[j + n], 0);
            }
        }

        /* (8) Unnormalize */
        // (u_{n-1}...u_{0})_{b} / 2^e
        let last_idx: usize = n - 1;
        r.vec[last_idx] = u_norm.vec[last_idx] >> e;
        for i in (0..last_idx).rev() {
            r.vec[i] = (((u_norm.vec[i + 1] as DDigit) << compl_e)
                | (u_norm.vec[i] >> e) as DDigit)
                as Digit;
        }

        q.trim();
        r.trim();
    }

    #[allow(dead_code)]
    fn div_algo_knuth(q: &mut Self, r: &mut Self, u: &Self, v: &Self) {
        Self::ddiv_algo_knuth(q, r, &u.vec, &v.vec);
    }

    pub(crate) fn ddivide(
        q: &mut Self,
        r: &mut Self,
        n: &[Digit],
        d: &[Digit],
        n_is_neg: bool,
        d_is_neg: bool,
    ) {
        if d.is_empty() {
            panic!("Division by zero attempt.");
        }

        let size_n = n.len();
        let size_d = d.len();

        // |N| < |D| case
        if (size_n == size_d && n[size_n - 1] < d[size_d - 1])
            || size_n < size_d
        {
            q.make_zero(); // |N| < |D| ==> |N| / |D| < 1 ==> Q computes to 0
            r.vec = n.to_vec(); // Computation (a/b)*b + a%b should equal a ==>
                                // a%b is a.
            r.neg = n_is_neg;
            return;
        }

        // TRUE: size_n >= size_d > 0

        // Ensure enough space in Q and R
        let size_q = size_n - size_d + 1_usize;
        q.vec.resize(size_q, 0);
        r.vec.resize(size_d, 0);

        // Unsigned integer division algorithms
        if size_d == 1 {
            // Knuth (Vol. 2, 4.3.1, p. 272) recommends using the algorithm used
            // in div_algo_single() when size_D is 1.
            Self::ddiv_algo_single(q, r, n, d);
        } else {
            Self::ddiv_algo_knuth(q, r, n, d);
            // Self::div_algo_binary(q, r, n, d);
        }

        q.neg = d_is_neg ^ n_is_neg;
        r.neg = r.size() > 0 && n_is_neg;
    }

    pub(crate) fn fddivide(
        q: &mut Self,
        r: &mut Self,
        n: &[Digit],
        d: &[Digit],
        n_sign: i32,
        d_sign: i32,
    ) {
        Self::ddivide(q, r, n, d, false, false);
        if d_sign == -1 {
            r.negate_mut();
        }
        match (n_sign, d_sign) {
            (1, -1) | (-1, 1) => {
                if r.is_zero() {
                    q.negate_mut();
                } else {
                    q.negate_mut();
                    *q -= 1;
                    r.negate_mut();
                    r.iadd_with_arbi_like_view(ArbiLikeView {
                        vec: d,
                        neg: d_sign == -1,
                    }); // *r += d;
                }
            }
            _ => {}
        }
    }

    /// `Q = N / D, R = N % D`, in one pass.
    /// Panics if the divisor is zero.
    ///
    /// (ISO/IEC 2020, 7.6.6, C++):
    /// > The binary / operator yields the quotient, and the binary % operator
    /// > yields the remainder from the division of the first expression by the
    /// > second. If the second operand of / or % is zero the behavior is
    /// > undefined. For integral operands the / operator yields the algebraic
    /// > quotient with any fractional part discarded; if the quotient a/b is
    /// > representable in the type of the result, (a/b)*b + a%b is equal to a;
    /// > otherwise, the behavior of both a/b and a%b is undefined.
    // Truncating Division
    pub(crate) fn tdivide(q: &mut Self, r: &mut Self, n: &Self, d: &Self) {
        Self::ddivide(q, r, &n.vec, &d.vec, n.is_negative(), d.is_negative());
    }

    // Floor Division
    pub(crate) fn fdivide(q: &mut Self, r: &mut Self, n: &Self, d: &Self) {
        Self::fddivide(q, r, &n.vec, &d.vec, n.signum(), d.signum());
    }
}

/// See the [`div()`](#method.div) method.
impl Div<Arbi> for Arbi {
    type Output = Arbi;

    fn div(self, rhs: Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, &self, &rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> Div<&'a Arbi> for Arbi {
    type Output = Arbi;

    fn div(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, &self, rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> Div<&'a Arbi> for &Arbi {
    type Output = Arbi;

    fn div(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Arbi::tdivide(&mut quot, &mut rem, self, rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl DivAssign<Arbi> for Arbi {
    fn div_assign(&mut self, rhs: Arbi) {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, self, &rhs);
        *self = quot;
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> DivAssign<&'a Arbi> for Arbi {
    fn div_assign(&mut self, rhs: &'a Arbi) {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, self, rhs);
        *self = quot;
    }
}

/// See the [`div()`](#method.div) method.
impl Rem<Arbi> for Arbi {
    type Output = Arbi;

    fn rem(self, rhs: Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, &self, &rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> Rem<&'a Arbi> for Arbi {
    type Output = Arbi;

    fn rem(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, &self, rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> Rem<&'a Arbi> for &Arbi {
    type Output = Arbi;

    fn rem(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Arbi::tdivide(&mut quot, &mut rem, self, rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl RemAssign<Arbi> for Arbi {
    fn rem_assign(&mut self, rhs: Arbi) {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, self, &rhs);
        *self = rem;
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> RemAssign<&'a Arbi> for Arbi {
    fn rem_assign(&mut self, rhs: &'a Arbi) {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, self, rhs);
        *self = rem;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_division_small() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let c = Arbi::from(2);

        assert_eq!(&a / &c, 5);
        assert_eq!(&b / &c, -2);
        assert_eq!(&a / &b, -2);
    }

    #[test]
    fn test_division_assignment_small() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);

        a /= &b;
        assert_eq!(a, -2);

        let mut c = Arbi::from(49);
        c /= c.clone();
        assert_eq!(c, 1);
    }

    #[test]
    fn test_modulus_small() {
        let a = Arbi::from(10);
        let b = Arbi::from(3);

        assert_eq!(a % b, 1);
    }

    #[test]
    fn test_modulus_assignment_small() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(3);
        a %= &b;
        assert_eq!(a, 1);

        let mut c = 49;
        c %= c.clone();
        assert_eq!(c, 0);
    }
}

impl Arbi {
    /// Computes both the quotient and remainder of division of this `Arbi`
    /// object by another `Arbi` object and returns both the quotient and the
    /// remainder as a pair.
    ///
    /// In Rust, [integer division rounds towards zero](https://doc.rust-lang.org/reference/expressions/operator-expr.html#arithmetic-and-logical-binary-operators)
    /// and given `remainder = dividend % divisor`, `remainder` will have the
    /// same sign as the `dividend`. The behavior of division in this crate is
    /// consistent with that of division of integer primitive types.
    ///
    /// Generally speaking, division algorithms calculate both the quotient and
    /// remainder simultaneously. If you need both, it is best to ask for both
    /// in one step rather than use the / and % operators in turn.
    ///
    /// # Parameters
    /// - `other`: The divisor.
    ///
    /// # Panic
    ///
    /// <div class="warning">
    /// Panics if a division by zero attempt is detected, consistent with the
    /// built-in behavior of dividing a primitive integer value by zero.
    /// </div>
    ///
    /// # Return
    /// A pair of `Arbi` integers where the first element is the quotient and
    /// the second element is the remainder.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Assign};
    ///
    /// let num = Arbi::from_str_radix(
    ///     "100000000000000000000000000000000000000000000000000",
    ///     16,
    /// )
    /// .unwrap();
    /// let mut den =
    ///     Arbi::from_str_radix("40000000000000000000000000000000000000", 16)
    ///         .unwrap();
    ///
    /// let (quo, rem) = num.divrem(&den);
    /// assert_eq!(quo, 1125899906842624_u64);
    /// assert_eq!(rem, 0);
    ///
    /// if let Err(e) = den.assign_str_radix(
    ///     "-10b67ec03f7d363506c60c8c877b6f92be8f41518c16aa3187",
    ///     16,
    /// ) {
    ///     panic!("Parse error: {}", e);
    /// }
    ///
    /// let (quo, rem) = num.divrem(&den);
    /// let expected_rem = Arbi::from_str_radix(
    ///     "54e92bc47a9d2e49a6543c40fc47666d59b2c38caac071917",
    ///     16,
    /// )
    /// .unwrap();
    /// assert_eq!(quo, -15);
    /// assert_eq!(rem, expected_rem);
    ///
    /// // We can also use the / and % operators in turn to get the same result,
    /// // but that would involve two passes through the division algorithm.
    /// assert_eq!(&num / &den, -15);
    /// assert_eq!(&num % &den, expected_rem);
    /// ```
    ///
    /// Dividing an `Arbi` integer by zero panics:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let x = Arbi::from_str_radix("123456789", 10).unwrap();
    /// let (quo, rem) = x.divrem(&Arbi::zero());
    /// ```
    ///
    /// Dividing a primitive integer value by zero panics:
    /// ```should_panic
    /// #![allow(unconditional_panic)]
    /// let zero = 0;
    /// let x = -123456789 / zero;
    /// ```
    ///
    /// ## Complexity
    /// \\( O(m \cdot n) \\)
    pub fn divrem(&self, other: &Arbi) -> (Arbi, Arbi) {
        let mut quot: Arbi = Arbi::zero();
        let mut rem: Arbi = Arbi::zero();
        Self::tdivide(&mut quot, &mut rem, self, other);
        (quot, rem)
    }
}

#[cfg(test)]
mod test_divrem {
    use super::*;
    use crate::base::BASE10;
    // use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::SDDigit;

    #[test]
    #[should_panic = "Division by zero attempt."]
    fn test_div_by_zero() {
        Arbi::from(10).divrem(&Arbi::zero());
    }

    #[test]
    fn test_misc() {
        let (quot, rem) = Arbi::from(10).divrem(&Arbi::from(-2));
        assert_eq!(quot, -5);
        assert_eq!(rem, 0);

        let (quot, rem) = Arbi::from(SDDigit::MIN).divrem(&Arbi::neg_one());
        assert_eq!(quot, 1 as DDigit + SDDigit::MAX as DDigit);
        assert_eq!(rem, 0);

        let (quot, rem) = Arbi::from(10).divrem(&Arbi::from(3));
        assert_eq!(quot, 3);
        assert_eq!(rem, 1);

        let (a_in, b_in) =
            (13565672763181344623_u128, 10964129492588451979_u128);
        let (quot, rem) = Arbi::from(a_in).divrem(&Arbi::from(b_in));
        assert_eq!(quot, a_in / b_in);
        assert_eq!(rem, a_in % b_in);
    }

    /* If Digit::BITS == 32, TRUE:
     * q_hat * vpp > Arbi::BASE * r_hat + u_norm[j+n-2]) and q_hat < Arbi::BASE */
    #[test]
    fn test_branch_a() {
        let a = Arbi::from_str_base("237634993259031120016359157450036169713011146626949272664357175750540350033099851627590", BASE10).unwrap();
        let b = Arbi::from_str_base("62391207566730956436059735556895094403209083705277492693463432131493682000515", BASE10).unwrap();

        let (quot, rem) = a.divrem(&b);

        assert_eq!(quot, 3808789772_i64);
        assert_eq!(rem, Arbi::from_str_base("16137245666917264679909410073093944632796496071688924192091054946917820895010", BASE10).unwrap());
    }

    /* If Digit::BITS == 32, TRUE:
     * q_hat * vpp > Arbi::BASE * r_hat + u_norm[j+n-2]) and q_hat == Arbi::BASE */
    #[test]
    fn test_branch_b() {
        let a =
            Arbi::from_str_base("1208925820177561948258300", BASE10).unwrap();
        let b = Arbi::from_str_base("281474976841724", BASE10).unwrap();

        let (quot, rem) = a.divrem(&b);

        assert_eq!(quot, 4294967295_u64);
        assert_eq!(rem, 281474976841720_u64);
    }

    #[test]
    fn test_add_back_step_of_knuth_algo_d() {
        let a = Arbi::from_str_base("1188654551471331072704702840834", BASE10)
            .unwrap();
        let b =
            Arbi::from_str_base("77371252455336267181195265", BASE10).unwrap();

        let (quot, rem) = a.divrem(&b);

        assert_eq!(quot, 15362);
        assert_eq!(rem, 77371252455336267181179904_u128);
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let udist_sd =
            get_uniform_die(SDigit::MIN as SQDigit, SDigit::MAX as SQDigit);
        let udist_sdd =
            get_uniform_die(SDDigit::MIN as SQDigit, SDDigit::MAX as SQDigit);
        let udist_sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            for (udist, mn) in &[
                (udist_sd, SDigit::MIN as SQDigit),
                (udist_sdd, SDDigit::MIN as SQDigit),
                (udist_sqd, SQDigit::MIN),
            ] {
                let (a_in, b_in) =
                    (udist.sample(&mut rng), udist.sample(&mut rng));
                let (a, b) = (Arbi::from(a_in), Arbi::from(b_in));

                if b == 0 {
                    // assert panic
                    continue;
                }
                if a == *mn && b == -1 {
                    continue;
                }

                let (quot, rem) = a.divrem(&b);

                assert_eq!(
                    quot,
                    a_in / b_in,
                    "Quot mismatch for a_in: {}, b_in: {}",
                    a_in,
                    b_in
                );
                assert_eq!(
                    rem,
                    a_in % b_in,
                    "Rem mismatch for a_in: {}, b_in: {}",
                    a_in,
                    b_in
                );
            }
        }
    }
}

/* !impl_arbi_div_for_primitive */
macro_rules! impl_arbi_div_for_primitive {
    ($(($signed_type:ty, $test_module:ident)),*) => {
        $(

impl Div<$signed_type> for Arbi {
    type Output = Self;
    #[allow(unused_comparisons)]
    fn div(self, other: $signed_type) -> Self {
        match other.to_digits() {
            None => panic!("Division by zero attempt."),
            Some(v) => {
                let v_len: usize = length_digits(&v);
                let mut quo = Arbi::zero();
                let mut rem = Arbi::zero();
                Self::ddivide(
                    &mut quo,
                    &mut rem,
                    &self.vec,
                    &v[..v_len],
                    self.is_negative(),
                    other < 0,
                );
                quo
            }
        }
    }
}

impl Div<&$signed_type> for Arbi {
    type Output = Self;
    fn div(self, other: &$signed_type) -> Self {
        self / (*other)
    }
}

impl Div<$signed_type> for &Arbi {
    type Output = Arbi;
    fn div(self, other: $signed_type) -> Arbi {
        self.clone() / other
    }
}

impl Div<&$signed_type> for &Arbi {
    type Output = Arbi;
    fn div(self, other: &$signed_type) -> Arbi {
        self.clone() / (*other)
    }
}

impl DivAssign<&$signed_type> for Arbi {
    fn div_assign(&mut self, other: &$signed_type) {
        (*self) /= *other;
    }
}

impl DivAssign<$signed_type> for Arbi {
    #[allow(unused_comparisons)]
    fn div_assign(&mut self, other: $signed_type) {
        match other.to_digits() {
            None => panic!("Division by zero attempt."),
            Some(v) => {
                let v_len: usize = length_digits(&v);
                let mut quo = Arbi::zero();
                let mut rem = Arbi::zero();
                Self::ddivide(
                    &mut quo,
                    &mut rem,
                    &self.vec,
                    &v[..v_len],
                    self.is_negative(),
                    other < 0,
                );
                *self = quo;
            }
        }
    }
}

impl Rem<$signed_type> for Arbi {
    type Output = Self;
    #[allow(unused_comparisons)]
    fn rem(self, other: $signed_type) -> Self {
        match other.to_digits() {
            None => panic!("Division by zero attempt."),
            Some(v) => {
                let v_len: usize = length_digits(&v);
                let mut quo = Arbi::zero();
                let mut rem = Arbi::zero();
                Self::ddivide(
                    &mut quo,
                    &mut rem,
                    &self.vec,
                    &v[..v_len],
                    self.is_negative(),
                    other < 0,
                );
                rem
            }
        }
    }
}

impl Rem<&$signed_type> for Arbi {
    type Output = Self;
    fn rem(self, other: &$signed_type) -> Self {
        self % (*other)
    }
}

impl Rem<$signed_type> for &Arbi {
    type Output = Arbi;
    fn rem(self, other: $signed_type) -> Arbi {
        self.clone() % other
    }
}

impl Rem<&$signed_type> for &Arbi {
    type Output = Arbi;
    fn rem(self, other: &$signed_type) -> Arbi {
        self.clone() % (*other)
    }
}

impl RemAssign<&$signed_type> for Arbi {
    fn rem_assign(&mut self, other: &$signed_type) {
        (*self) %= *other;
    }
}

impl RemAssign<$signed_type> for Arbi {
    #[allow(unused_comparisons)]
    fn rem_assign(&mut self, other: $signed_type) {
        match other.to_digits() {
            None => panic!("Division by zero attempt."),
            Some(v) => {
                let v_len: usize = length_digits(&v);
                let mut quo = Arbi::zero();
                let mut rem = Arbi::zero();
                Self::ddivide(
                    &mut quo,
                    &mut rem,
                    &self.vec,
                    &v[..v_len],
                    self.is_negative(),
                    other < 0,
                );
                *self = rem;
            }
        }
    }
}

impl Div<Arbi> for $signed_type {
    type Output = Arbi;
    fn div(self, other: Arbi) -> Self::Output {
        self / &other
    }
}

impl Div<&Arbi> for $signed_type {
    type Output = Arbi;
    fn div(self, other: &Arbi) -> Self::Output {
        let num = Arbi::from(self);
        num / other
    }
}

impl Div<Arbi> for &$signed_type {
    type Output = Arbi;
    fn div(self, other: Arbi) -> Self::Output {
        (*self) / other
    }
}

impl Div<&Arbi> for &$signed_type {
    type Output = Arbi;
    fn div(self, other: &Arbi) -> Self::Output {
        (*self) / other
    }
}

impl Rem<Arbi> for $signed_type {
    type Output = Arbi;
    fn rem(self, other: Arbi) -> Self::Output {
        self % &other
    }
}

impl Rem<&Arbi> for $signed_type {
    type Output = Arbi;
    fn rem(self, other: &Arbi) -> Self::Output {
        let num = Arbi::from(self);
        num % other
    }
}

impl Rem<Arbi> for &$signed_type {
    type Output = Arbi;
    fn rem(self, other: Arbi) -> Self::Output {
        (*self) % other
    }
}

impl Rem<&Arbi> for &$signed_type {
    type Output = Arbi;
    fn rem(self, other: &Arbi) -> Self::Output {
        (*self) % other
    }
}

#[cfg(test)]
mod $test_module {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{SDDigit, SDigit};

    #[test]
    #[should_panic = "Division by zero attempt."]
    fn test_div_by_zero() {
        let zero = 0 as $signed_type;
        let n = Arbi::from(-123456789);
        let _ = n / zero;
    }

    #[test]
    #[should_panic = "Division by zero attempt."]
    fn test_rem_by_zero() {
        let zero = 0 as $signed_type;
        let n = Arbi::from(-123456789);
        let _ = n % zero;
    }

    #[test]
    #[should_panic = "Division by zero attempt."]
    fn test_div_by_zero_ref() {
        let zero = 0 as $signed_type;
        let n = Arbi::from(-123456789);
        let _ = &n / zero;
    }

    #[test]
    #[should_panic = "Division by zero attempt."]
    fn test_rem_by_zero_ref() {
        let zero = 0 as $signed_type;
        let n = Arbi::from(-123456789);
        let _ = &n % zero;
    }

    macro_rules! test_div_rem {
        ($lhs:expr, $r:expr) => {{
            if ($lhs as i128 == i128::MIN) && ($r as i128 == -1) {
                continue;
            }

            let mut lhs_arbi = Arbi::from($lhs);
            let expected_div = $lhs as SDDigit / $r as SDDigit;
            let expected_rem = $lhs as SDDigit % $r as SDDigit;

            assert_eq!(&lhs_arbi / $r, expected_div);
            assert_eq!(&lhs_arbi % $r, expected_rem);
            assert_eq!(lhs_arbi.clone() / $r, expected_div);
            assert_eq!(lhs_arbi.clone() % $r, expected_rem);

            let mut lhs_arbi_clone = lhs_arbi.clone();
            lhs_arbi_clone /= $r;
            assert_eq!(lhs_arbi_clone, expected_div);
            lhs_arbi %= $r;
            assert_eq!(lhs_arbi, expected_rem);
        }};
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        // let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        let die = get_uniform_die(<$signed_type>::MIN, <$signed_type>::MAX);
        for _ in 0..i16::MAX {
            let r = die.sample(&mut rng);
            if !fits_in_i64(r) {
                continue;
            }
            if r == 0 {
                continue;
            }

            let lhs = die_sdigit.sample(&mut rng);
            test_div_rem!(lhs, r);

            let lhs = die_sddigit.sample(&mut rng);
            test_div_rem!(lhs, r);

            // let lhs = die_sqdigit.sample(&mut rng);
            // test_div_rem!(lhs, r);
        }
    }

    macro_rules! test_div_rem_prim_lhs {
        ($lhs:expr, $rhs:expr) => {{
            if $rhs == 0 {
                continue;
            }
            let rhs_arbi = Arbi::from($rhs);
            let expected_div = $lhs as SDDigit / $rhs as SDDigit;
            let expected_rem = $lhs as SDDigit % $rhs as SDDigit;
            assert_eq!($lhs / &rhs_arbi, expected_div);
            assert_eq!($lhs % &rhs_arbi, expected_rem);
            assert_eq!($lhs / rhs_arbi.clone(), expected_div);
            assert_eq!($lhs % rhs_arbi, expected_rem);
        }};
    }

    #[test]
    fn smoke_primitive_on_lhs() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(<$signed_type>::MIN, <$signed_type>::MAX);
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        // let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
        for _ in 0..i16::MAX {
            let lhs = die.sample(&mut rng);
            if !fits_in_i64(lhs) {
                continue;
            }

            // let rhs = die_sqdigit.sample(&mut rng);
            // test_div_rem_prim_lhs!(lhs, rhs);

            let rhs = die_sddigit.sample(&mut rng);
            test_div_rem_prim_lhs!(lhs, rhs);

            let rhs = die_sdigit.sample(&mut rng);
            test_div_rem_prim_lhs!(lhs, rhs);
        }
    }
}

        )*
    }
}
/* impl_arbi_div_for_primitive! */

impl_arbi_div_for_primitive![
    (i8, test_i8),
    (u8, test_u8),
    (i16, test_i16),
    (u16, test_u16),
    (i32, test_i32),
    (u32, test_u32),
    (i64, test_i64),
    (u64, test_u64),
    (i128, test_i128),
    (u128, test_u128),
    (isize, test_isize),
    (usize, test_usize)
];

#[allow(dead_code)]
pub(crate) fn fits_in_i128<T>(num: T) -> bool
where
    T: PartialOrd + Copy + core::convert::TryInto<i128>,
{
    num.try_into().is_ok()
}

#[allow(dead_code)]
pub(crate) fn fits_in_i64<T>(num: T) -> bool
where
    T: PartialOrd + Copy + core::convert::TryInto<i64>,
{
    num.try_into().is_ok()
}
