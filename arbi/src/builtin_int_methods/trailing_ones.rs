/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount, Digit};

impl Arbi {
    /// Returns the number of trailing ones in the binary representation of the
    /// absolute value of `self`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.trailing_ones(), 0);
    /// let a = Arbi::from(u128::MAX);
    /// assert_eq!(a.trailing_ones(), 128);
    /// let b = Arbi::from(u128::MAX - 1);
    /// assert_eq!(b.trailing_ones(), 0);
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn trailing_ones(&self) -> BitCount {
        let first_nonmax =
            self.vec.iter().position(|&digit| digit != Digit::MAX);
        if let Some(idx) = first_nonmax {
            self.vec[idx].trailing_ones() as BitCount
                + idx as BitCount * Digit::BITS as BitCount
        } else {
            self.size() as BitCount * Digit::BITS as BitCount
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign};
    use crate::{BitCount, DDigit, Digit, QDigit};

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
                digit.trailing_ones() as BitCount
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
