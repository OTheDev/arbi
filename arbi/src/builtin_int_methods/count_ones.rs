/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// If this integer is nonnegative, returns the number of ones in the binary
    /// representation of `self`. Otherwise, returns `None`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(-1).count_ones(), None);
    /// assert_eq!(Arbi::from(0).count_ones(), Some(0));
    /// assert_eq!(Arbi::from(1).count_ones(), Some(1));
    /// assert_eq!(Arbi::from(0b01001100u32).count_ones(), Some(3));
    /// assert_eq!(Arbi::from(u64::MAX).count_ones(), Some(64));
    /// ```
    ///
    /// # Note
    /// Theoretically, arbitrary precision (signed) integers have an unbounded
    /// number of sign bits.
    ///
    /// Thus, this function returns `None` if the integer is negative.
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn count_ones(&self) -> Option<BitCount> {
        if self.is_negative() {
            None
        } else {
            Some(self.count_ones_abs())
        }
    }

    #[inline]
    pub(crate) fn count_ones_abs(&self) -> BitCount {
        self.vec.iter().map(|x| x.count_ones() as u128).sum()
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign};
    use crate::{BitCount, DDigit, Digit, QDigit};

    #[test]
    fn test_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);

        for _ in 0..i16::MAX {
            let digit = die_d.sample(&mut rng);
            let digit_arbi = Arbi::from(digit);
            assert_eq!(
                digit_arbi.count_ones(),
                Some(BitCount::from(digit.count_ones()))
            );

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(
                ddigit_arbi.count_ones(),
                Some(BitCount::from(ddigit.count_ones()))
            );
        }
    }

    #[test]
    fn test_special() {
        let zero = Arbi::zero();
        assert_eq!(zero.count_ones(), Some(BitCount::from(0_u32.count_ones())));

        let mut a = Arbi::from(Digit::MAX - 1);
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from((Digit::MAX - 1).count_ones()))
        );

        a.assign(Digit::MAX);
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from(Digit::MAX.count_ones()))
        );

        a.incr();
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from((Digit::MAX as DDigit + 1).count_ones()))
        );

        a.assign(DDigit::MAX - 1);
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from((DDigit::MAX - 1).count_ones()))
        );

        a.assign(DDigit::MAX);
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from(DDigit::MAX.count_ones() as u128))
        );

        a.assign(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.count_ones(),
            Some(BitCount::from((DDigit::MAX as QDigit + 1).count_ones()))
        );
    }
}
