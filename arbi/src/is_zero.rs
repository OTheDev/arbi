/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Return `true` if this integer is zero, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert!(zero.is_zero());
    /// let one = Arbi::one();
    /// assert!(!one.is_zero());
    /// let neg_one = Arbi::neg_one();
    /// assert!(!neg_one.is_zero());
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.vec.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    fn test_is_zero() {
        let zero = Arbi::zero();
        assert!(zero.is_zero());
        let one = Arbi::one();
        assert!(!one.is_zero());
        let neg_one = Arbi::neg_one();
        assert!(!neg_one.is_zero());
    }
}
