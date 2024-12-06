/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Reverses the order of bits in the absolute value of the integer.
    ///
    /// The least significant bit becomes the most significant bit, second least
    /// significant bit becomes second most-significant bit, etc.
    ///
    /// The sign remains unchanged.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(0x12345678_u32);
    /// assert_eq!(a.reverse_bits(), 0x12345678_u32.reverse_bits());
    /// ```
    ///
    /// # Complexity
    /// \\( O(n) \\)
    pub fn reverse_bits(mut self) -> Self {
        self.reverse_bits_mut();
        self
    }

    /// Reverses the order of bits in the absolute value of the integer.
    ///
    /// The least significant bit becomes the most significant bit, second least
    /// significant bit becomes second most-significant bit, etc.
    ///
    /// The sign remains unchanged.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(0x12345678_u32);
    /// a.reverse_bits_mut();
    /// assert_eq!(a, 0x12345678_u32.reverse_bits());
    /// ```
    pub fn reverse_bits_mut(&mut self) {
        let len = self.vec.len();
        for i in 0..(len / 2) {
            self.vec[i] = self.vec[i].reverse_bits();
            self.vec[len - 1 - i] = self.vec[len - 1 - i].reverse_bits();
            self.vec.swap(i, len - 1 - i);
        }
        if len % 2 != 0 {
            self.vec[len / 2] = self.vec[len / 2].reverse_bits();
        }
        self.trim();
    }

    /// Reverses the order of bits in the absolute value of the integer.
    ///
    /// The least significant bit becomes the most significant bit, second least
    /// significant bit becomes second most-significant bit, etc.
    ///
    /// The sign remains unchanged.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(0x12345678_u32);
    /// let b: Arbi = a.reverse_bits_ref();
    /// assert_eq!(b, 0x12345678_u32.reverse_bits());
    /// ```
    pub fn reverse_bits_ref(&self) -> Self {
        let ret = self.clone();
        ret.reverse_bits()
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{DDigit, Digit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_d = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_dd = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);

        for _ in 0..i16::MAX {
            let digit = die_d.sample(&mut rng);
            let digit_arbi = Arbi::from(digit);
            assert_eq!(digit_arbi.reverse_bits(), digit.reverse_bits() as u128);

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(
                ddigit_arbi.reverse_bits(),
                ddigit.reverse_bits() as u128
            );
        }
    }

    #[test]
    fn boundaries() {
        let zero = Arbi::zero();
        assert_eq!(zero.reverse_bits(), 0_u32.reverse_bits() as u128);

        let a = Arbi::from(Digit::MAX - 1);
        assert_eq!(a.reverse_bits(), (Digit::MAX - 1).reverse_bits() as u128);

        let a = Arbi::from(Digit::MAX);
        assert_eq!(a.reverse_bits(), Digit::MAX.reverse_bits() as u128);

        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(
            a.clone().reverse_bits(),
            (Digit::MAX as DDigit + 1).reverse_bits() as u128
        );

        let a = Arbi::from(DDigit::MAX - 1);
        assert_eq!(a.reverse_bits(), (DDigit::MAX - 1).reverse_bits() as u128);

        let a = Arbi::from(DDigit::MAX);
        assert_eq!(a.reverse_bits(), DDigit::MAX.reverse_bits() as u128);
    }
}
