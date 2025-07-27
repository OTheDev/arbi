/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// If this integer is nonnegative, returns the number of ones in its binary
    /// representation. Otherwise, returns `None`.
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
        self.vec.iter().map(|x| x.count_ones() as BitCount).sum()
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, Assign};
    use crate::{BitCount, DDigit, Digit, QDigit, SDDigit, SDigit, SQDigit};

    macro_rules! assert_count_ones_big {
        ($value:expr, $T:ty) => {
            #[allow(unused_comparisons)] // for unsigned types
            {
                let value = $value;
                assert_eq!(
                    Arbi::from(value).count_ones(),
                    if value >= <$T>::ZERO {
                        Some(BitCount::from(value.count_ones() as u32))
                    } else {
                        None
                    }
                );
            }
        };
    }

    macro_rules! assert_count_ones {
        ($value:expr) => {
            #[allow(unused_comparisons)] // for unsigned types
            {
                let value = $value;
                assert_eq!(
                    Arbi::from(value).count_ones(),
                    if value >= 0 {
                        Some(BitCount::from(value.count_ones() as u32))
                    } else {
                        None
                    }
                );
            }
        };
    }

    #[test]
    fn test_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qd = crate::util::qdigit::get_uniform_qdigit_die(
            QDigit::from(DDigit::MAX) + QDigit::from(1u8),
            QDigit::MAX,
        );
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sdd = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqd = crate::util::qdigit::get_uniform_sqdigit_die(
            SQDigit::MIN,
            SQDigit::MAX,
        );

        for _ in 0..i16::MAX {
            assert_count_ones!(die_d.sample(&mut rng));
            assert_count_ones!(die_dd.sample(&mut rng));
            assert_count_ones!(die_sd.sample(&mut rng));
            assert_count_ones!(die_sdd.sample(&mut rng));
            #[cfg(not(target_pointer_width = "64"))]
            {
                assert_count_ones!(die_qd.sample(&mut rng));
                assert_count_ones!(die_sqd.sample(&mut rng));
            }
            #[cfg(target_pointer_width = "64")]
            {
                assert_count_ones_big!(die_qd.sample(&mut rng), QDigit);
                assert_count_ones_big!(die_sqd.sample(&mut rng), SQDigit);
            }
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

        a += 1;
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
            Some(BitCount::from(DDigit::MAX.count_ones()))
        );

        // a.assign(DDigit::MAX as QDigit + 1);
        // assert_eq!(
        //     a.count_ones(),
        //     Some(BitCount::from((DDigit::MAX as QDigit + 1).count_ones()))
        // );
    }
}
