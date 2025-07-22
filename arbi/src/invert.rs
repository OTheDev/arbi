/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Return the inverse of `self` modulo `modulus`, if it exists. Otherwise,
    /// return `None`.
    ///
    /// Mathematically, if the inverse exists, the return value, \\( r \\),
    /// will be such that \\( 0 \leq r \lt |\text{modulus}| \\) (\\( 0 \\)
    /// only if \\( |\text{modulus}| = 1 \\)). Thus, the result may be negative.
    ///
    /// # Panic
    /// Panics if `modulus` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let (a, ma) = (Arbi::from(3), Arbi::from(-3));
    /// let (b, mb) = (Arbi::from(11), Arbi::from(-11));
    ///
    /// let i = a.invert_ref(&b).unwrap();
    /// assert_eq!(i, 4);
    ///
    /// let i = ma.invert_ref(&b).unwrap();
    /// assert_eq!(i, 7);
    ///
    /// let i = a.invert_ref(&mb).unwrap();
    /// assert_eq!(i, 4);
    ///
    /// let i = ma.invert_ref(&mb).unwrap();
    /// assert_eq!(i, 7);
    ///
    /// assert_eq!(a.invert_ref(&Arbi::one()).unwrap(), 0);
    /// assert_eq!(a.invert_ref(&Arbi::neg_one()).unwrap(), 0);
    ///
    /// assert_eq!(Arbi::zero().invert_ref(&a), None);
    /// assert_eq!(Arbi::zero().invert_ref(&ma), None);
    /// ```
    ///
    /// Panics if `modulus` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    /// Arbi::from(7).invert_ref(&Arbi::zero());
    /// ```
    pub fn invert_ref(&self, modulus: &Self) -> Option<Self> {
        assert!(!modulus.is_zero(), "division by zero attempt");
        if modulus.size() == 1 && modulus.vec[0] == 1 {
            // Modulus is -1 or 1
            return Some(Self::zero());
        }
        /* Assumes m > 1 */
        let (mut q, mut r) = (Arbi::zero(), Arbi::zero());
        let mut a = self.clone();
        let mut s = Self::one();
        let mut t = Self::zero();
        let mut m = modulus.clone();
        while !m.is_zero() {
            // Floor division, treating m as positive
            Self::fddivide(&mut q, &mut r, &a.vec, &m.vec, a.signum(), 1);
            a = m;
            m = core::mem::take(&mut r);
            let nt = s - core::mem::take(&mut q) * &t;
            s = t;
            t = nt;
        }
        if a != 1 {
            // Inverse does not exist
            return None;
        }
        /* At this point, s is an inverse to self modulo |modulus| such that
         * |s| < |modulus|. Now adjust for potentially negative modulus
         */
        // NOTE: If we are happy with 0 <= |r| < |modulus|, just return this:
        // match (modulus.is_negative(), s.is_negative()) {
        //     (true, false) | (false, true) => Some(s + modulus),
        //     _ => Some(s),
        // }
        // However, we want 0 <= r < |modulus|.
        let mut x = s % modulus;
        if x.is_negative() {
            if modulus.is_negative() {
                x -= modulus;
            } else {
                x += modulus;
            }
        }
        Some(x)
    }
}
