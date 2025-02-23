/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount, Digit};

impl Arbi {
    /// If this integer is *not* `-1`, returns the number of trailing ones in
    /// the binary representation (two's complement) of `self`. Otherwise,
    /// returns `None`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // nonnegative
    /// assert_eq!(Arbi::zero().trailing_ones(), Some(0));
    /// assert_eq!(Arbi::from(u128::MAX).trailing_ones(), Some(128));
    /// assert_eq!(Arbi::from(u128::MAX - 1).trailing_ones(), Some(0));
    ///
    /// // negative
    /// assert_eq!(Arbi::from(-1).trailing_ones(), None);
    /// assert_eq!(Arbi::from(-7).trailing_ones(), Some(1));
    /// assert_eq!(Arbi::from(-5).trailing_ones(), Some(2));
    /// assert_eq!(Arbi::from(-121).trailing_ones(), Some(3));
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn trailing_ones(&self) -> Option<BitCount> {
        if !self.is_negative() {
            let first_nonmax =
                self.vec.iter().position(|&digit| digit != Digit::MAX);
            if let Some(idx) = first_nonmax {
                Some(
                    self.vec[idx].trailing_ones() as BitCount
                        + idx as BitCount * Digit::BITS as BitCount,
                )
            } else {
                Some(self.size() as BitCount * Digit::BITS as BitCount)
            }
        } else {
            if self.vec[0].trailing_zeros() != 0 {
                return Some(0);
            } else if self.vec[0] == 1 && self.size() == 1 {
                return None; // -1
            }
            let mut digit = self.vec[0].wrapping_sub(1);
            let mut idx = 0;
            if digit == 0 {
                idx = 1;
                while idx < self.size() {
                    digit = self.vec[idx];
                    if digit != 0 {
                        break;
                    }
                    idx += 1;
                }
            }
            Some(
                digit.trailing_zeros() as BitCount
                    + idx as BitCount * Digit::BITS as BitCount,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign};
    use crate::{BitCount, DDigit, Digit, QDigit, SDDigit, SDigit, SQDigit};

    macro_rules! test_uniform_die {
        ($die:expr, $rng:expr, unsigned) => {{
            let val = $die.sample($rng);
            let arbi = Arbi::from(val);
            assert_eq!(
                arbi.trailing_ones(),
                Some(BitCount::from(val.trailing_ones()))
            );
        }};
        ($die:expr, $rng:expr) => {{
            let val = $die.sample($rng);
            let arbi = Arbi::from(val);
            assert_eq!(
                arbi.trailing_ones(),
                if val == -1 {
                    None
                } else {
                    Some(BitCount::from(val.trailing_ones()))
                }
            );
        }};
    }

    #[test]
    fn test_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qd = get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sdd = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            test_uniform_die!(die_d, &mut rng, unsigned);
            test_uniform_die!(die_dd, &mut rng, unsigned);
            test_uniform_die!(die_qd, &mut rng, unsigned);
            test_uniform_die!(die_sd, &mut rng);
            test_uniform_die!(die_sdd, &mut rng);
            test_uniform_die!(die_sqd, &mut rng);
        }
    }

    #[test]
    fn test_ones_sequence_positive() {
        // 1, 11, 111, ...
        // j = 1: 2^1 - 1 = 1 (0b1)
        // j = 2: 2^2 - 1 = 3 (0b11)
        // j = 3: 2^3 - 1 = 7 (0b111)
        // ...
        // j = k: 2^k - 1 has binary representation 0b{k ones}
        for j in 1..u128::BITS {
            let ones = (1u128 << j) - 1;
            let arbi = Arbi::from(ones);
            assert_eq!(arbi.trailing_ones(), Some(BitCount::from(j)));

            let zeros = !ones;
            let arbi = Arbi::from(zeros);
            assert_eq!(arbi.trailing_ones(), Some(0));
        }

        let arbi = Arbi::from(u128::MAX);
        assert_eq!(arbi.trailing_ones(), Some(BitCount::from(u128::BITS)));
    }

    #[test]
    fn test_ones_sequence_negative() {
        // 0 trailing ones
        assert_eq!((-2i128).trailing_ones(), 0);
        assert_eq!(Arbi::from(-2i128).trailing_ones(), Some(0));
        // 1 trailing one, 2 trailing ones, ..., 126 trailing ones
        // (10 ... 01), (10 ... 011), 10 ... 0111, ..., 101 ... 1
        for j in 1..=126 {
            let val = (-1i128 << j) ^ i128::MAX;
            let arbi = Arbi::from(val);
            assert_eq!(arbi.trailing_ones(), Some(j));
            assert_eq!(
                arbi.trailing_ones(),
                Some(BitCount::from(val.trailing_ones()))
            );
        }
        // 1 ... 1 (128 trailing ones)
        assert_eq!((-1i128).trailing_ones(), 128);
        assert_eq!(Arbi::from(-1i128).trailing_ones(), None);
    }

    #[test]
    fn test_special_nonnegative() {
        let zero = Arbi::zero();
        assert_eq!(
            zero.trailing_ones(),
            Some(BitCount::from(0_u32.trailing_ones()))
        );

        let mut a = Arbi::from(Digit::MAX - 1);
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from((Digit::MAX - 1).trailing_ones()))
        );

        a.assign(Digit::MAX);
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from(Digit::MAX.trailing_ones()))
        );

        a += 1;
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from((Digit::MAX as DDigit + 1).trailing_ones()))
        );

        a.assign(DDigit::MAX - 1);
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from((DDigit::MAX - 1).trailing_ones()))
        );

        a.assign(DDigit::MAX);
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from(DDigit::MAX.trailing_ones()))
        );

        a.assign(DDigit::MAX as QDigit + 1);
        assert_eq!(
            a.trailing_ones(),
            Some(BitCount::from((DDigit::MAX as QDigit + 1).trailing_ones()))
        );
    }
}
