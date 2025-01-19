/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Return `true` if this integer is odd, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert!(!zero.is_odd());
    /// let a = Arbi::from(-123456789);
    /// assert!(a.is_odd());
    /// let b = Arbi::from(-12345678);
    /// assert!(!b.is_odd());
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_odd(&self) -> bool {
        if self.size() == 0 {
            false
        } else {
            (self.vec[0] & 1) != 0
        }
    }

    /// Return `true` if this integer is even, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert!(zero.is_even());
    /// let a = Arbi::from(-12345678);
    /// assert!(a.is_even());
    /// let b = Arbi::from(-123456789);
    /// assert!(!b.is_even());
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_even(&self) -> bool {
        !self.is_odd()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Arbi, DDigit, Digit, SDDigit};

    #[test]
    fn test_even_or_odd() {
        let mut arbi: Arbi;

        arbi = Arbi::zero();
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());

        arbi = Arbi::from(Digit::MAX);
        assert!(arbi.is_odd());
        assert!(!arbi.is_even());

        arbi = Arbi::from(Digit::MAX as DDigit + 1);
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());

        arbi = Arbi::from(-(Digit::MAX as SDDigit));
        assert!(arbi.is_odd());
        assert!(!arbi.is_even());

        arbi -= 1;
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());
    }
}
