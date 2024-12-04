/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::cmp::Ordering;

impl Arbi {
    /// Returns a number representing the sign of `self`.
    /// - `0` if the number if zero.
    /// - `1` if the number if positive.
    /// - `-1` if the number is negative.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.signum(), 0);
    /// assert_eq!(0i32.signum(), 0);
    ///
    /// let one = Arbi::from(1);
    /// assert_eq!(one.signum(), 1);
    /// assert_eq!(1i32.signum(), 1);
    ///
    /// let minus_one = Arbi::from(-1);
    /// assert_eq!(minus_one.signum(), -1);
    /// assert_eq!((-1i32).signum(), -1);
    /// ```
    pub fn signum(&self) -> i32 {
        match self.sign() {
            Ordering::Equal => 0,
            Ordering::Greater => 1,
            Ordering::Less => -1,
        }
    }
}
