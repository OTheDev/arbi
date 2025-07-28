/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Returns `true` if `self` is positive and `false` if the number is zero
    /// or negative.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let neg = Arbi::from(-1234);
    /// let pos = Arbi::from(1234);
    /// let zer = Arbi::zero();
    ///
    /// assert!(!neg.is_positive());
    /// assert!(pos.is_positive());
    /// assert!(!zer.is_positive());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_positive(&self) -> bool {
        !self.neg && !self.is_zero()
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero
    /// or positive.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let neg = Arbi::from(-1234);
    /// let pos = Arbi::from(1234);
    /// let zer = Arbi::zero();
    ///
    /// assert!(neg.is_negative());
    /// assert!(!pos.is_negative());
    /// assert!(!zer.is_negative());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_negative(&self) -> bool {
        self.neg
    }
}

#[cfg(test)]
mod tests {
    use crate::util::qdigit::get_uniform_sqdigit_die;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, SDDigit, SDigit, SQDigit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqdigit = get_uniform_sqdigit_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_sdigit.sample(&mut rng);
            let a = Arbi::from(r);

            assert_eq!(a.is_negative(), r.is_negative());
            assert_eq!(a.is_positive(), r.is_positive());

            let r = die_sddigit.sample(&mut rng);
            let a = Arbi::from(r);

            assert_eq!(a.is_negative(), r.is_negative());
            assert_eq!(a.is_positive(), r.is_positive());

            let r = die_sqdigit.sample(&mut rng);
            let a = Arbi::from(r);

            assert_eq!(a.is_negative(), r.is_negative());
            assert_eq!(a.is_positive(), r.is_positive());
        }
    }
}
