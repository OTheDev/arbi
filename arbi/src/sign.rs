/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::cmp::Ordering;

impl Arbi {
    /// Return an `Ordering` indicating the sign of the number: `Ordering::Less`
    /// for negative, `Ordering::Equal` for zero, `Ordering::Greater` for
    /// positive.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// use core::cmp::Ordering;
    ///
    /// let neg = Arbi::from(-123456789);
    /// let zer = Arbi::zero();
    /// let pos = Arbi::from(123456789);
    ///
    /// assert_eq!(neg.sign(), Ordering::Less);
    /// assert_eq!(zer.sign(), Ordering::Equal);
    /// assert_eq!(pos.sign(), Ordering::Greater);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn sign(&self) -> Ordering {
        if self.size() == 0 {
            Ordering::Equal
        } else if self.is_negative() {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;
    use core::cmp::Ordering;

    #[test]
    fn test_sign() {
        let zero = Arbi::zero();
        assert_eq!(zero.sign(), Ordering::Equal);

        let one = Arbi::one();
        assert_eq!(one.sign(), Ordering::Greater);

        let neg_one = Arbi::neg_one();
        assert_eq!(neg_one.sign(), Ordering::Less);
    }
}
