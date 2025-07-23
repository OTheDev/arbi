/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Divide `self` by `rhs`, returning both a quotient and remainder:
    /// `(q, r)`.
    ///
    /// The quotient is rounded towards negative infinity and the remainder will
    /// have the same sign as `rhs`.
    ///
    /// # Panic
    /// Panics if `rhs` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let (a, b) = (Arbi::from(8), Arbi::from(3));
    /// let (ma, mb) = (a.negate_ref(), b.negate_ref());
    ///
    /// let (q, r) = a.divrem_floor_ref(&b);
    /// assert_eq!(q, 2);
    /// assert_eq!(r, 2);
    ///
    /// let (q, r) = a.divrem_floor_ref(&mb);
    /// assert_eq!(q, -3);
    /// assert_eq!(r, -1);
    ///
    /// let (q, r) = ma.divrem_floor_ref(&b);
    /// assert_eq!(q, -3);
    /// assert_eq!(r, 1);
    ///
    /// let (q, r) = ma.divrem_floor_ref(&mb);
    /// assert_eq!(q, 2);
    /// assert_eq!(r, -2);
    ///
    /// let (q, r) = Arbi::zero().divrem_floor_ref(&a);
    /// assert_eq!(q, 0);
    /// assert_eq!(r, 0);
    ///
    /// let (q, r) = Arbi::zero().divrem_floor_ref(&ma);
    /// assert_eq!(q, 0);
    /// assert_eq!(r, 0);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let x = Arbi::from(123456789);
    /// let (q, r) = x.divrem_floor_ref(&Arbi::zero());
    /// ```
    pub fn divrem_floor_ref(&self, rhs: &Self) -> (Self, Self) {
        let (mut q, mut r) = (Arbi::zero(), Arbi::zero());
        Self::fdivide(&mut q, &mut r, self, rhs);
        (q, r)
    }
}
