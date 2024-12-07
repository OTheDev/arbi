/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use alloc::vec::Vec;

impl Arbi {
    /// Return an `Arbi` integer with value `0`.
    ///
    /// No memory allocation occurs.
    ///
    /// [`Arbi::new()`], [`Arbi::zero()`], and [`Arbi::default()`] are
    /// equivalent, except that `Arbi::default()` is not `const`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::new();
    /// assert_eq!(zero, 0);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub const fn new() -> Self {
        Arbi {
            vec: Vec::new(),
            neg: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    fn test_new() {
        let zero = Arbi::new();
        assert_eq!(zero, 0);
        assert!(zero.vec.is_empty());
        assert!(!zero.neg);
    }
}
