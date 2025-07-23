/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Returns `true` if `self` is an integer multiple of `rhs`, and `false`
    /// otherwise.
    ///
    /// If both `self` and `rhs` are zero, returns `true`. If `self` is nonzero
    /// and `rhs` is zero, returns `false`. Otherwise, this function is
    /// equivalent to `self % rhs == 0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert!(Arbi::from(8).is_multiple_of(&Arbi::from(4)));
    /// assert!(!Arbi::from(7).is_multiple_of(&Arbi::from(4)));
    /// assert!(Arbi::from(0).is_multiple_of(&Arbi::from(0)));
    /// assert!(!Arbi::from(7).is_multiple_of(&Arbi::from(0)));
    /// ```
    pub fn is_multiple_of(&self, rhs: &Self) -> bool {
        if rhs.is_zero() {
            self.is_zero()
        } else {
            (self % rhs).is_zero()
        }
    }
}
