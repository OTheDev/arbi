/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount, Digit};

impl Arbi {
    /// If the integer is nonzero, returns the number of trailing zeros in the
    /// binary representation of `self`. Otherwise, returns `None`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.trailing_zeros(), None);
    /// let a = Arbi::from(0xFFFFFFFF00000000u64);
    /// assert_eq!(a.trailing_zeros(), Some(32));
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn trailing_zeros(&self) -> Option<BitCount> {
        let first_nonzero = self.vec.iter().position(|&digit| digit != 0)?;
        Some(
            self.vec[first_nonzero].trailing_zeros() as BitCount
                + first_nonzero as BitCount * Digit::BITS as BitCount,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{BitCount, DDigit, Digit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);

        for _ in 0..i16::MAX {
            let digit = die_d.sample(&mut rng);
            let digit_arbi = Arbi::from(digit);
            assert_eq!(
                digit_arbi.trailing_zeros(),
                if digit == 0 {
                    None
                } else {
                    Some(digit.trailing_zeros() as BitCount)
                }
            );

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(
                ddigit_arbi.trailing_zeros(),
                if ddigit == 0 {
                    None
                } else {
                    Some(ddigit.trailing_zeros() as BitCount)
                }
            );
        }
    }

    #[test]
    fn special() {
        let zero = Arbi::zero();
        assert_eq!(zero.trailing_zeros(), None);

        let neg_one = Arbi::neg_one();
        assert_eq!(
            neg_one.trailing_zeros(),
            Some((-1_i32).trailing_zeros() as BitCount)
        );

        let one = Arbi::one();
        assert_eq!(
            one.trailing_zeros(),
            Some(1_i32.trailing_zeros() as BitCount)
        );
    }
}
