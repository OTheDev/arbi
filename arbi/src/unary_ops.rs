/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

/// Negate `self` in-place and return `self`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(123456789);
/// let b = -a;
/// assert_eq!(b, -123456789);
/// ```
///
/// # Complexity
/// \\( O(1) \\)
impl core::ops::Neg for Arbi {
    type Output = Self;
    fn neg(mut self) -> Self {
        if self.size() != 0 {
            self.neg = !self.neg;
        }
        self
    }
}

/// Return a new `Arbi` integer representing `self` negated.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(123456789);
/// let b = -&a; // Cloning occurs
/// assert_eq!(b, -123456789);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl core::ops::Neg for &Arbi {
    type Output = Arbi;
    fn neg(self) -> Arbi {
        if self.size() != 0 {
            let ret = self.clone();
            -ret
        } else {
            Arbi::zero()
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Arbi;

    #[test]
    fn test_unary_minus() {
        let a = Arbi::from(10);
        let b = Arbi::from(-10);
        let z = Arbi::zero();
        assert_eq!(-a, -10);
        assert_eq!(-b, 10);
        assert_eq!(-z, 0);
    }

    #[test]
    fn test_unary_minus_reference() {
        let a = Arbi::from(10);
        let b = Arbi::from(-10);
        let z = Arbi::zero();
        assert_eq!(-(&a), -10);
        assert_eq!(-(&b), 10);
        assert_eq!(-(&z), 0);
    }
}
