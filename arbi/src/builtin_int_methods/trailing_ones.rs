/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

impl Arbi {
    /// Returns the number of trailing ones in the binary representation of the
    /// absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.trailing_ones(), 0);
    ///
    /// let a = Arbi::from(u128::MAX);
    /// assert_eq!(a.trailing_ones(), 128);
    ///
    /// let b = Arbi::from(u128::MAX - 1);
    /// assert_eq!(b.trailing_ones(), 0);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn trailing_ones(&self) -> u128 {
        let mut sum = 0_u128;
        for x in self.vec.iter() {
            let trailing_ones = x.trailing_ones() as u128;
            sum += trailing_ones;
            if trailing_ones != Digit::BITS as u128 {
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
            assert_eq!(
                digit_arbi.trailing_ones(),
                digit.trailing_ones() as u128
            );

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(
                ddigit_arbi.trailing_ones(),
                ddigit.trailing_ones() as u128
            );
        }
    }

    #[test]
    fn boundaries() {
        let zero = Arbi::zero();
        assert_eq!(zero.trailing_ones(), 0_u32.trailing_ones() as u128);

        let mut a = Arbi::from(Digit::MAX - 1);
        assert_eq!(a.trailing_ones(), (Digit::MAX - 1).trailing_ones() as u128);

        a.assign(Digit::MAX);
        assert_eq!(a.trailing_ones(), Digit::MAX.trailing_ones() as u128);

        a.incr();
        assert_eq!(
            a.trailing_ones(),
            (Digit::MAX as DDigit + 1).trailing_ones() as u128
        );

        a.assign(DDigit::MAX - 1);
        assert_eq!(
            a.trailing_ones(),
            (DDigit::MAX - 1).trailing_ones() as u128
        );

        a.assign(DDigit::MAX);
        assert_eq!(a.trailing_ones(), DDigit::MAX.trailing_ones() as u128);

        a.assign(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.trailing_ones(),
            (DDigit::MAX as QDigit + 1).trailing_ones() as u128
        );
    }
}
