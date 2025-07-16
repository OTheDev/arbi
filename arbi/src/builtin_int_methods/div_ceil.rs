/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::cmp::Ordering;

impl Arbi {
    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// positive infinity.
    ///
    /// # Panics
    /// Panics if `rhs` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(7);
    /// let b = Arbi::from(-7);
    /// let c = Arbi::from(2);
    /// let d = Arbi::from(-2);
    ///
    /// assert_eq!(a.div_ceil_ref(&c), 4);
    /// assert_eq!(a.div_ceil_ref(&d), -3);
    /// assert_eq!(b.div_ceil_ref(&c), -3);
    /// assert_eq!(b.div_ceil_ref(&d), 4);
    /// ```
    pub fn div_ceil_ref(&self, rhs: &Self) -> Self {
        if self.is_zero() {
            return Arbi::zero();
        }

        match (self.sign(), rhs.sign()) {
            (Ordering::Greater, Ordering::Greater) => 1 + (self - 1) / rhs,
            (Ordering::Less, Ordering::Less) => 1 + (self + 1) / rhs,
            _ => self / rhs,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, SDDigit, SDigit, SQDigit};

    fn div_ceil(lhs: i128, rhs: i128) -> i128 {
        let (q, r) = (lhs / rhs, lhs % rhs);
        if r != 0 {
            q + (1 + ((lhs ^ rhs) >> (i128::BITS - 1)))
        } else {
            q
        }
    }

    #[test]
    #[should_panic]
    fn test_division_by_zero_panics() {
        Arbi::from(1).div_ceil_ref(&Arbi::zero());
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let udist_sd =
            get_uniform_die(SDigit::MIN as SQDigit, SDigit::MAX as SQDigit);
        let udist_sdd =
            get_uniform_die(SDDigit::MIN as SQDigit, SDDigit::MAX as SQDigit);
        let udist_sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            for (udist, mn) in &[
                (udist_sd, SDigit::MIN as SQDigit),
                (udist_sdd, SDDigit::MIN as SQDigit),
                (udist_sqd, SQDigit::MIN),
            ] {
                let (a_in, b_in) =
                    (udist.sample(&mut rng), udist.sample(&mut rng));
                let (a, b) = (Arbi::from(a_in), Arbi::from(b_in));

                if b == 0 {
                    continue;
                }
                if a == *mn && b == -1 {
                    continue;
                }

                let res = a.div_ceil_ref(&b);
                assert_eq!(
                    res,
                    div_ceil(a_in, b_in),
                    "Quot mismatch for a_in: {}, b_in: {}",
                    a_in,
                    b_in
                );
            }
        }
    }
}
