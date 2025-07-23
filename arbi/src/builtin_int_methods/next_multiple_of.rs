/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Assign};

impl Arbi {
    /// If `rhs` is positive, return the smallest value greater than or equal to
    /// `self` that is a multiple of `rhs`. If `rhs` is negative, return the
    /// largest value less than or equal to `self` that is a multiple of `rhs`.
    ///
    /// # Panic
    /// Panics if `rhs` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(12).next_multiple_of(&Arbi::from(6)), 12);
    /// assert_eq!(Arbi::from(19).next_multiple_of(&Arbi::from(7)), 21);
    /// assert_eq!(Arbi::from(25).next_multiple_of(&Arbi::from(-5)), 25);
    /// assert_eq!(Arbi::from(25).next_multiple_of(&Arbi::from(-7)), 21);
    /// assert_eq!(Arbi::from(-21).next_multiple_of(&Arbi::from(7)), -21);
    /// assert_eq!(Arbi::from(-25).next_multiple_of(&Arbi::from(7)), -21);
    /// assert_eq!(Arbi::from(-21).next_multiple_of(&Arbi::from(-7)), -21);
    /// assert_eq!(Arbi::from(-25).next_multiple_of(&Arbi::from(-7)), -28);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    /// Arbi::from(123).next_multiple_of(&Arbi::zero());
    /// ```
    pub fn next_multiple_of(&self, rhs: &Self) -> Self {
        let (_, mut r) = self.divrem_floor_ref(rhs);
        if r.is_zero() {
            r.assign(self);
            r
        } else {
            (rhs - r) + self
        }
    }

    /// If `rhs` is positive, return the largest value less than or equal to
    /// `self` that is a multiple of `rhs`. If `rhs` is negative, return the
    /// smallest value greater than or equal to `self` that is a multiple of
    /// `rhs`.
    ///
    /// # Panic
    /// Panics if `rhs` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(12).prev_multiple_of(&Arbi::from(6)), 12);
    /// assert_eq!(Arbi::from(19).prev_multiple_of(&Arbi::from(7)), 14);
    /// assert_eq!(Arbi::from(25).prev_multiple_of(&Arbi::from(-5)), 25);
    /// assert_eq!(Arbi::from(25).prev_multiple_of(&Arbi::from(-7)), 28);
    /// assert_eq!(Arbi::from(-21).prev_multiple_of(&Arbi::from(7)), -21);
    /// assert_eq!(Arbi::from(-25).prev_multiple_of(&Arbi::from(7)), -28);
    /// assert_eq!(Arbi::from(-21).prev_multiple_of(&Arbi::from(-7)), -21);
    /// assert_eq!(Arbi::from(-25).prev_multiple_of(&Arbi::from(-7)), -21);
    /// ```
    ///
    /// Panics if `rhs` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    /// Arbi::from(123).prev_multiple_of(&Arbi::zero());
    /// ```
    pub fn prev_multiple_of(&self, rhs: &Self) -> Self {
        let (_, mut r) = self.divrem_floor_ref(rhs);
        if r.is_zero() {
            // Potentially avoid memory allocation
            r.assign(self);
            r
        } else {
            self - r
        }
    }
}
