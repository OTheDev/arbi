/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

impl Arbi {
    /// Returns the number of leading ones in the binary representation of the
    /// absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.leading_ones(), 0);
    ///
    /// let a = Arbi::from(u128::MAX);
    /// assert_eq!(a.leading_ones(), 128);
    ///
    /// let b = Arbi::from(u128::MAX - 1);
    /// assert_eq!(b.leading_ones(), 127);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn leading_ones(&self) -> u128 {
        let mut sum = 0_u128;
        for x in self.vec.iter().rev() {
            let leading_ones = x.leading_ones() as u128;
            sum += leading_ones;
            if leading_ones != Digit::BITS as u128 {
                break;
            }
        }
        sum
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign};
    use crate::{DDigit, Digit, QDigit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);

        for _ in 0..i16::MAX {
            let digit = die_d.sample(&mut rng);
            let digit_arbi = Arbi::from(digit);
            assert_eq!(digit_arbi.leading_ones(), digit.leading_ones() as u128);

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(
                ddigit_arbi.leading_ones(),
                ddigit.leading_ones() as u128
            );
        }
    }

    #[test]
    fn boundaries() {
        let zero = Arbi::zero();
        assert_eq!(zero.leading_ones(), 0_u32.leading_ones() as u128);

        let mut a = Arbi::from(Digit::MAX - 1);
        assert_eq!(a.leading_ones(), (Digit::MAX - 1).leading_ones() as u128);

        a.assign(Digit::MAX);
        assert_eq!(a.leading_ones(), Digit::MAX.leading_ones() as u128);

        a.incr();
        assert_eq!(
            a.leading_ones(),
            (Digit::MAX as DDigit + 1).leading_ones() as u128
        );

        a.assign(DDigit::MAX - 1);
        assert_eq!(a.leading_ones(), (DDigit::MAX - 1).leading_ones() as u128);

        a.assign(DDigit::MAX);
        assert_eq!(a.leading_ones(), DDigit::MAX.leading_ones() as u128);

        a.assign(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.leading_ones(),
            (DDigit::MAX as QDigit + 1).leading_ones() as u128
        );
    }
}
