/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Negates the integer, in-place.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut pos = Arbi::from(123456789);
    /// pos = pos.negate();
    /// assert_eq!(pos, -123456789);
    /// pos = pos.negate();
    /// assert_eq!(pos, 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn negate(mut self) -> Self {
        self.negate_mut();
        self
    }

    /// Negates the integer, in-place.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut pos = Arbi::from(123456789);
    /// pos.negate_mut();
    /// assert_eq!(pos, -123456789);
    /// pos.negate_mut();
    /// assert_eq!(pos, 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn negate_mut(&mut self) {
        if self.size() > 0 {
            self.neg = !self.neg;
        }
    }

    /// Return a new integer representing this integer negated.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let pos = Arbi::from(123456789);
    /// assert_eq!(pos.negate_ref(), -123456789);
    /// let neg = Arbi::from(-123456789);
    /// assert_eq!(neg.negate_ref(), 123456789);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    #[inline(always)]
    pub fn negate_ref(&self) -> Self {
        let ret = self.clone();
        ret.negate()
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    fn test_negate_mut() {
        let mut a = Arbi::from(123);
        let mut z = Arbi::zero();

        // Zero
        z.negate_mut();
        assert_eq!(z, 0);

        // Positive
        a.negate_mut();
        assert_eq!(a, -123);

        // Negative
        a.negate_mut();
        assert_eq!(a, 123);

        a.negate_mut();
        a.negate_mut();
        assert_eq!(a, 123);
    }
}
