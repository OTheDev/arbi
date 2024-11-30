/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{uints::UnsignedUtilities, Arbi, Digit};

impl Arbi {
    /// If nonzero, return the number of bits required to represent its absolute
    /// value. Otherwise, return `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut a = Arbi::from(u128::MAX);
    /// assert_eq!(a.bit_length(), 128);
    ///
    /// a.incr();
    /// assert_eq!(a.bit_length(), 129);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    pub fn bit_length(&self) -> usize {
        if self.size() == 0 {
            0
        } else {
            (self.size() - 1) * (Digit::BITS as usize)
                + Digit::bit_length(*self.vec.last().unwrap()) as usize
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, QDigit};

    #[test]
    fn test_bit_length_returns_0_for_0() {
        assert_eq!(Arbi::zero().bit_length(), 0);
        assert_eq!(
            Arbi::zero().bit_length(),
            (u32::BITS - (0 as u32).leading_zeros()) as usize
        );
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let die_s = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_l = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_e = get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for i in 1..u16::MAX {
            assert_eq!(
                Arbi::from(i).bit_length(),
                (u16::BITS - i.leading_zeros()) as usize
            );

            let rs = die_s.sample(&mut rng);
            let rl = die_l.sample(&mut rng);
            let re = die_e.sample(&mut rng);

            assert_eq!(
                Arbi::from(rs).bit_length(),
                (Digit::BITS - rs.leading_zeros()) as usize
            );
            assert_eq!(
                Arbi::from(rl).bit_length(),
                (DDigit::BITS - rl.leading_zeros()) as usize
            );
            assert_eq!(
                Arbi::from(re).bit_length(),
                (QDigit::BITS - re.leading_zeros()) as usize
            );
        }
    }

    #[test]
    fn test_bit_length_spec() {
        let (pos, neg, zer, one) = (
            Arbi::from(16),
            Arbi::from(-16),
            Arbi::from(0),
            Arbi::from(1),
        );

        assert_eq!(pos.bit_length(), 5);
        assert_eq!(neg.bit_length(), 5);
        assert_eq!(zer.bit_length(), 0);
        assert_eq!(one.bit_length(), 1);

        assert_eq!(Arbi::from(u64::MAX).bit_length(), 64);
        assert_eq!(Arbi::from(i64::MIN).bit_length(), 64);
    }
}
