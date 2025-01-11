/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount};

impl Arbi {
    /// If this integer is negative, returns the number of zeros in its binary
    /// representation (two's complement). Otherwise, returns `None`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// assert_eq!(Arbi::from(1).count_zeros(), None);
    /// assert_eq!(Arbi::from(0).count_zeros(), None);
    /// assert_eq!(Arbi::from(-1).count_zeros(), Some(0)); // 1111 1111
    /// assert_eq!(Arbi::from(-2).count_zeros(), Some(1)); // 1111 1110
    /// assert_eq!(Arbi::from(-128).count_zeros(), Some(7)); // 1000 0000
    /// ```
    ///
    /// # Note
    /// Theoretically, arbitrary precision (signed) integers have an unbounded
    /// number of sign bits.
    ///
    /// Thus, this function returns `None` if the integer is nonnegative.
    ///
    /// If you need the number of zeros in the magnitude of the integer defined
    /// by the bit field `[0, size_bits())`, use [`Arbi::count_ones()`] combined
    /// with [`Arbi::size_bits()`].
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn count_zeros(&self) -> Option<BitCount> {
        if self.is_negative() {
            /* TODO: use single pass */
            Some(self.trailing_zeros().unwrap() + self.count_ones_abs() - 1)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{BitCount, DDigit, Digit, QDigit, SDDigit, SDigit, SQDigit};

    macro_rules! assert_count_zeros {
        ($value:expr) => {
            #[allow(unused_comparisons)] // for unsigned types
            {
                let value = $value;
                assert_eq!(
                    Arbi::from(value).count_zeros(),
                    if value >= 0 {
                        None
                    } else {
                        Some(BitCount::from(value.count_zeros()))
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
        let die_qd = get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sdd = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            assert_count_zeros!(die_d.sample(&mut rng));
            assert_count_zeros!(die_dd.sample(&mut rng));
            assert_count_zeros!(die_qd.sample(&mut rng));
            assert_count_zeros!(die_sd.sample(&mut rng));
            assert_count_zeros!(die_sdd.sample(&mut rng));
            assert_count_zeros!(die_sqd.sample(&mut rng));
        }
    }
}
