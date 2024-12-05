/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Calculates the quotient of Euclidean division of `self` by `rhs`.
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

    /// Calculates the least nonnegative remainder of self (mod rhs).
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
