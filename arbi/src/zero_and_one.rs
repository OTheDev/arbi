/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// A constant `Arbi` integer representing `0`.
    pub const ZERO: Arbi = Arbi::new();

    /// Equivalent to [`Arbi::new()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero, 0);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub const fn zero() -> Self {
        Arbi::new()
    }

    /// Return an `Arbi` integer representing `1`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let one = Arbi::one();
    /// assert_eq!(one, 1);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn one() -> Self {
        Arbi::from(1)
    }

    /// Return an `Arbi` integer representing `-1`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let neg_one = Arbi::neg_one();
    /// assert_eq!(neg_one, -1);
    /// ```
    ///
    /// # Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn neg_one() -> Self {
        Arbi::from(-1)
    }
}
