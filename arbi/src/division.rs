/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, DDigit, Digit, SDDigit};

impl Arbi {
    fn div_algo_single(q: &mut Self, r: &mut Self, u: &Self, v: &Self) {
        let mut rem: DDigit = 0;

        for j in (0..u.vec.len()).rev() {
            let temp: DDigit = (rem << Digit::BITS) | u.vec[j] as DDigit; // rem * Arbi::BASE + u[j]
            q.vec[j] = (temp / v.vec[0] as DDigit) as Digit;
            rem = temp % v.vec[0] as DDigit;
        }

        r.vec[0] = rem as Digit;

        q.trim();
        r.trim();
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
        for i in (0_usize..u.bit_length()).rev() {
            // (3)(I)
            *r <<= 1_usize;

            // (3)(II)
            if u.test_bit(i) {
                r.set_bit(0_usize);
            }

            // (3)(III)
            if Arbi::cmp_abs(r, v) != core::cmp::Ordering::Less {
                // (3)(III)(a)
                // *r = &(*r) - v;
                Arbi::sub_abs_inplace(r, v, false);
                // (3)(III)(b)
                q.set_bit(i);
            }
        }
    }

    fn div_algo_knuth(q: &mut Self, r: &mut Self, u: &Self, v: &Self) {
        let m = u.size();
        let n = v.size();

        const BASE: DDigit = Digit::MAX as DDigit + 1;
        const B_HALF: Digit = (BASE >> 1) as Digit;

        /* (1) Normalize */
        // Find e such that b > 2^{e} * v_{n-1} >= b / 2
        let v_msd: Digit = v.vec[n - 1];
        let mut e: u32 = 0;
        while (v_msd << e) < B_HALF {
            e += 1;
        }

        let compl_e: u32 = Digit::BITS - e;

        let mut u_norm = Arbi::default();
        let mut v_norm = Arbi::default();
        u_norm.vec.resize(m + 1, 0);
        v_norm.vec.resize(n, 0);

        // u_norm set to u * 2^{e}. Cast to ddigit as e may be 0 which would be
        // UB
        u_norm.vec[0] = u.vec[0] << e;
        for i in 1..m {
            u_norm.vec[i] = (((u.vec[i] as DDigit) << e)
                | (u.vec[i - 1] as DDigit >> compl_e as DDigit))
                as Digit;
        }
        u_norm.vec[m] = (u.vec[m - 1] as DDigit >> compl_e) as Digit;

        // v_norm set to v * 2^{e}
        v_norm.vec[0] = v.vec[0] << e;
        for i in 1..n {
            v_norm.vec[i] = (((v.vec[i] as DDigit) << e)
                | (v.vec[i - 1] as DDigit >> compl_e as DDigit))
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
    fn divide(q: &mut Self, r: &mut Self, n: &Self, d: &Self) {
        if d.size() == 0 {
            panic!("Division by zero attempt.");
        }

        let size_n = n.size();
        let size_d = d.size();

        // |N| < |D| case
        if (size_n == size_d && n.vec[size_n - 1] < d.vec[size_d - 1])
            || size_n < size_d
        {
            q.make_zero(); // |N| < |D| ==> |N| / |D| < 1 ==> Q computes to 0
            *r = n.clone(); // Computation (a/b)*b + a%b should equal a ==> a%b
                            // is a.
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
            Self::div_algo_single(q, r, n, d);
        } else {
            Self::div_algo_knuth(q, r, n, d);
            // Self::div_algo_binary(q, r, n, d);
        }

        q.neg = d.negative() ^ n.negative();
        r.neg = r.size() > 0 && n.negative();
    }
}

/// See the [`div()`](#method.div) method.
impl core::ops::Div<Arbi> for Arbi {
    type Output = Arbi;

    fn div(self, rhs: Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, &self, &rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::Div<&'a Arbi> for Arbi {
    type Output = Arbi;

    fn div(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, &self, rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::Div<&'a Arbi> for &Arbi {
    type Output = Arbi;

    fn div(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Arbi::divide(&mut quot, &mut rem, self, rhs);
        quot
    }
}

/// See the [`div()`](#method.div) method.
impl core::ops::DivAssign<Arbi> for Arbi {
    fn div_assign(&mut self, rhs: Arbi) {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, self, &rhs);
        *self = quot;
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::DivAssign<&'a Arbi> for Arbi {
    fn div_assign(&mut self, rhs: &'a Arbi) {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, self, rhs);
        *self = quot;
    }
}

/// See the [`div()`](#method.div) method.
impl core::ops::Rem<Arbi> for Arbi {
    type Output = Arbi;

    fn rem(self, rhs: Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, &self, &rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::Rem<&'a Arbi> for Arbi {
    type Output = Arbi;

    fn rem(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, &self, rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::Rem<&'a Arbi> for &Arbi {
    type Output = Arbi;

    fn rem(self, rhs: &'a Arbi) -> Arbi {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Arbi::divide(&mut quot, &mut rem, self, rhs);
        rem
    }
}

/// See the [`div()`](#method.div) method.
impl core::ops::RemAssign<Arbi> for Arbi {
    fn rem_assign(&mut self, rhs: Arbi) {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, self, &rhs);
        *self = rem;
    }
}

/// See the [`div()`](#method.div) method.
impl<'a> core::ops::RemAssign<&'a Arbi> for Arbi {
    fn rem_assign(&mut self, rhs: &'a Arbi) {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, self, rhs);
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
    /// let (quo, rem) = num.div(&den);
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
    /// let (quo, rem) = num.div(&den);
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
    /// let (quo, rem) = x.div(&Arbi::zero());
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
    pub fn div(&self, other: &Arbi) -> (Arbi, Arbi) {
        let mut quot: Arbi = Arbi::default();
        let mut rem: Arbi = Arbi::default();
        Self::divide(&mut quot, &mut rem, self, other);
        (quot, rem)
    }
}

#[cfg(test)]
mod test_divrem {
    use super::*;
    use crate::base::BASE10;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{SDDigit, SDigit, SQDigit};

    #[test]
    #[should_panic]
    fn test_div_by_zero() {
        Arbi::from(10).div(&Arbi::zero());
    }

    #[test]
    fn test_misc() {
        let (quot, rem) = Arbi::from(10).div(&Arbi::from(-2));
        assert_eq!(quot, -5);
        assert_eq!(rem, 0);

        let (quot, rem) = Arbi::from(SDDigit::MIN).div(&Arbi::from(-1));
        assert_eq!(quot, 1 as DDigit + SDDigit::MAX as DDigit);
        assert_eq!(rem, 0);

        let (quot, rem) = Arbi::from(10).div(&Arbi::from(3));
        assert_eq!(quot, 3);
        assert_eq!(rem, 1);

        let (a_in, b_in) =
            (13565672763181344623_u128, 10964129492588451979_u128);
        let (quot, rem) = Arbi::from(a_in).div(&Arbi::from(b_in));
        assert_eq!(quot, a_in / b_in);
        assert_eq!(rem, a_in % b_in);
    }

    /* If Digit::BITS == 32, TRUE:
     * q_hat * vpp > Arbi::BASE * r_hat + u_norm[j+n-2]) and q_hat < Arbi::BASE */
    #[test]
    fn test_branch_a() {
        let a = Arbi::from_str_base("237634993259031120016359157450036169713011146626949272664357175750540350033099851627590", BASE10).unwrap();
        let b = Arbi::from_str_base("62391207566730956436059735556895094403209083705277492693463432131493682000515", BASE10).unwrap();

        let (quot, rem) = a.div(&b);

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

        let (quot, rem) = a.div(&b);

        assert_eq!(quot, 4294967295_u64);
        assert_eq!(rem, 281474976841720_u64);
    }

    #[test]
    fn test_add_back_step_of_knuth_algo_d() {
        let a = Arbi::from_str_base("1188654551471331072704702840834", BASE10)
            .unwrap();
        let b =
            Arbi::from_str_base("77371252455336267181195265", BASE10).unwrap();

        let (quot, rem) = a.div(&b);

        assert_eq!(quot, 15362);
        assert_eq!(rem, 77371252455336267181179904_u128);
    }

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

                let (quot, rem) = a.div(&b);

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
