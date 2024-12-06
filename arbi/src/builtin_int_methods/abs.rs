/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Computes the absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let neg = Arbi::from(-123456789);
    /// assert_eq!(neg.abs(), 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn abs(mut self) -> Arbi {
        if self.neg {
            self.negate();
        }
        self
    }

    /// Computes the absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let neg = Arbi::from(-123456789);
    /// assert_eq!(neg.abs_ref(), 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    #[inline(always)]
    pub fn abs_ref(&self) -> Arbi {
        let mut ret = self.clone();
        if self.neg {
            ret.negate();
        }
        ret
    }

    /// Computes the absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut neg = Arbi::from(-123456789);
    /// neg.abs_mut();
    /// assert_eq!(neg, 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn abs_mut(&mut self) {
        if self.neg {
            self.neg = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    fn test_abs() {
        let pos = Arbi::from(123);
        assert_eq!(123, pos.abs());

        let neg = Arbi::from(-123);
        assert_eq!(123, neg.abs());

        let zer = Arbi::zero();
        assert_eq!(0, zer.abs());
    }

    #[test]
    fn test_abs_mut() {
        let mut pos = Arbi::from(123);
        pos.abs_mut();
        assert_eq!(pos, 123);

        let mut neg = Arbi::from(-123);
        neg.abs_mut();
        assert_eq!(neg, 123);

        let mut zer = Arbi::zero();
        zer.abs_mut();
        assert_eq!(zer, 0);
    }

    #[test]
    fn test_abs_ref() {
        let pos = Arbi::from(123);
        assert_eq!(pos.abs_ref(), 123);

        let neg = Arbi::from(-123);
        assert_eq!(neg.abs_ref(), 123);

        let zer = Arbi::zero();
        assert_eq!(zer.abs_ref(), 0);
    }
}
