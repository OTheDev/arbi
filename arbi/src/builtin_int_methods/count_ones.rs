/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Returns the number of ones in the binary representation of the absolute
    /// value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::from(0b01001100u32);
    /// assert_eq!(a.count_ones(), 3);
    ///
    /// let max_u64 = Arbi::from(u64::MAX);
    /// assert_eq!(max_u64.count_ones(), 64);
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.count_ones(), 0);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn count_ones(&self) -> u128 {
        self.vec.iter().map(|x| x.count_ones() as u128).sum()
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
            assert_eq!(digit_arbi.count_ones(), digit.count_ones() as u128);

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(ddigit_arbi.count_ones(), ddigit.count_ones() as u128);
        }
    }

    #[test]
    fn boundaries() {
        let zero = Arbi::zero();
        assert_eq!(zero.count_ones(), 0_u32.count_ones() as u128);

        let mut a = Arbi::from(Digit::MAX - 1);
        assert_eq!(a.count_ones(), (Digit::MAX - 1).count_ones() as u128);

        a.assign(Digit::MAX);
        assert_eq!(a.count_ones(), Digit::MAX.count_ones() as u128);

        a.incr();
        assert_eq!(
            a.count_ones(),
            (Digit::MAX as DDigit + 1).count_ones() as u128
        );

        a.assign(DDigit::MAX - 1);
        assert_eq!(a.count_ones(), (DDigit::MAX - 1).count_ones() as u128);

        a.assign(DDigit::MAX);
        assert_eq!(a.count_ones(), DDigit::MAX.count_ones() as u128);

        a.assign(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.count_ones(),
            (DDigit::MAX as QDigit + 1).count_ones() as u128
        );
    }
}
