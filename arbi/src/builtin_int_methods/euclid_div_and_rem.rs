/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Calculates the quotient of Euclidean division of `self` by `rhs`.
    ///
    /// # See also
    /// - [`div_euclid()`](https://doc.rust-lang.org/std/primitive.i64.html#method.div_euclid)
    ///     for built-in integer types.
    /// - [`Arbi::divrem_euclid()`].
    ///
    /// # Panics
    /// This function will panic if `rhs` is `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut a = Arbi::from(9);
    /// let mut b = Arbi::from(5);
    ///
    /// assert_eq!(a.div_euclid(&b), 1);
    ///
    /// b.negate();
    /// assert_eq!(a.div_euclid(&b), -1);
    ///
    /// a.negate();
    /// b.negate();
    /// assert_eq!(a.div_euclid(&b), -2);
    ///
    /// b.negate();
    /// assert_eq!(a.div_euclid(&b), 2);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let num = Arbi::from(9);
    /// let den = Arbi::zero();
    /// num.div_euclid(&den);
    /// ```
    ///
    /// # Complexity
    /// \\( O(m \cdot n) \\)
    pub fn div_euclid(&self, rhs: &Self) -> Arbi {
        let (quot, _) = self.divrem_euclid(rhs);
        quot
    }

    /// Calculates the least nonnegative remainder of `self (mod rhs)`.
    ///
    /// # See also
    /// - [`rem_euclid()`](https://doc.rust-lang.org/std/primitive.i64.html#method.rem_euclid)
    ///     for built-in integer types.
    /// - [`Arbi::divrem_euclid()`].
    ///
    /// # Panics
    /// This function will panic if `rhs` is `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut a = Arbi::from(9);
    /// let mut b = Arbi::from(5);
    ///
    /// assert_eq!(a.rem_euclid(&b), 4);
    ///
    /// b.negate();
    /// assert_eq!(a.rem_euclid(&b), 4);
    ///
    /// a.negate();
    /// b.negate();
    /// assert_eq!(a.rem_euclid(&b), 1);
    ///
    /// b.negate();
    /// assert_eq!(a.rem_euclid(&b), 1);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let num = Arbi::from(9);
    /// let den = Arbi::zero();
    /// num.rem_euclid(&den);
    /// ```
    ///
    /// # Complexity
    /// \\( O(m \cdot n) \\)
    pub fn rem_euclid(&self, rhs: &Self) -> Arbi {
        let (_, rem) = self.divrem_euclid(rhs);
        rem
    }

    // TODO: see if we need to increase the reserve amount to minimize
    // allocations. Also, see if we can do all of this in the same pass as the
    // main algo.

    /// Same as `(self.div_euclid(rhs), self.rem_euclid(rhs))`, but in one pass.
    ///
    /// # Panics
    /// This function will panic if `rhs` is `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut a = Arbi::from(9);
    /// let mut b = Arbi::from(5);
    ///
    /// let (quo, rem) = a.divrem_euclid(&b);
    /// assert!(quo == 1 && rem == 4);
    ///
    /// b.negate();
    /// let (quo, rem) = a.divrem_euclid(&b);
    /// assert!(quo == -1 && rem == 4);
    ///
    /// a.negate();
    /// b.negate();
    /// let (quo, rem) = a.divrem_euclid(&b);
    /// assert!(quo == -2 && rem == 1);
    ///
    /// b.negate();
    /// let (quo, rem) = a.divrem_euclid(&b);
    /// assert!(quo == 2 && rem == 1);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let num = Arbi::from(9);
    /// let den = Arbi::zero();
    /// num.divrem_euclid(&den);
    /// ```
    ///
    /// # Complexity
    /// \\( O(m \cdot n) \\)
    pub fn divrem_euclid(&self, rhs: &Self) -> (Arbi, Arbi) {
        let (mut quot, mut rem) = self.div(rhs);
        if rem.is_negative() {
            if rhs.is_negative() {
                // rhs < 0
                rem -= rhs;
                quot.incr();
            } else {
                // rhs > 0
                rem += rhs;
                quot.decr();
            }
        }
        (quot, rem)
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, SDDigit, SDigit, SQDigit};

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
                    continue;
                }
                if a == *mn && b == -1 {
                    continue;
                }

                let (quot, rem) = a.divrem_euclid(&b);

                assert_eq!(
                    quot,
                    a_in.div_euclid(b_in),
                    "Quot mismatch for a_in: {}, b_in: {}",
                    a_in,
                    b_in
                );
                assert_eq!(
                    rem,
                    a_in.rem_euclid(b_in),
                    "Rem mismatch for a_in: {}, b_in: {}",
                    a_in,
                    b_in
                );
            }
        }
    }
}