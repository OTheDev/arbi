/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Computes the absolute difference between `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(8000).abs_diff(Arbi::from(10000)), 2000);
    /// assert_eq!(Arbi::from(-10000).abs_diff(Arbi::from(8000)), 18000);
    /// assert_eq!(Arbi::from(-10000).abs_diff(Arbi::from(-11000)), 1000);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn abs_diff(self, other: Self) -> Self {
        let mut ret = if self.size() > other.size() {
            self - other
        } else {
            other - self
        };
        ret.abs_mut();
        ret
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Assign};
    ///
    /// let mut a = Arbi::from(8000);
    ///
    /// let b = Arbi::from(10000);
    /// a.abs_diff_mut(&b);
    /// assert_eq!(a, 2000);
    ///
    /// a.assign(-10000);
    /// let b = Arbi::from(8000);
    /// a.abs_diff_mut(&b);
    /// assert_eq!(a, 18000);
    ///
    /// a.assign(-10000);
    /// let b = Arbi::from(-11000);
    /// a.abs_diff_mut(&b);
    /// assert_eq!(a, 1000);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn abs_diff_mut(&mut self, other: &Self) {
        *self -= other;
        self.abs_mut();
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(8000).abs_diff_ref(&Arbi::from(10000)), 2000);
    /// assert_eq!(Arbi::from(-10000).abs_diff_ref(&Arbi::from(8000)), 18000);
    /// assert_eq!(Arbi::from(-10000).abs_diff_ref(&Arbi::from(-11000)), 1000);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn abs_diff_ref(&self, other: &Self) -> Self {
        let clone: Arbi;
        let mut ret: Arbi;
        if self.size() > other.size() {
            clone = self.clone();
            ret = clone - other;
        } else {
            clone = other.clone();
            ret = clone - self;
        }
        ret.abs_mut();
        ret
    }
}
