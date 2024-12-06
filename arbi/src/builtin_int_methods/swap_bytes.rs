/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Reverses the byte order of the absolute value of the integer.
    ///
    /// The sign remains unchanged.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(0x12345678_u32);
    /// assert_eq!(a.swap_bytes(), 0x78563412);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn swap_bytes(mut self) -> Self {
        self.swap_bytes_mut();
        self
    }

    /// See [`Arbi::swap_bytes()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut a = Arbi::from(0x12345678_u32);
    /// a.swap_bytes_mut();
    /// assert_eq!(a, 0x78563412);
    /// ```
    pub fn swap_bytes_mut(&mut self) {
        let len = self.vec.len();
        for i in 0..(len / 2) {
            self.vec[i] = self.vec[i].swap_bytes();
            self.vec[len - 1 - i] = self.vec[len - 1 - i].swap_bytes();
            self.vec.swap(i, len - 1 - i);
        }
        if len % 2 != 0 {
            self.vec[len / 2] = self.vec[len / 2].swap_bytes();
        }
        self.trim();
    }

    /// See [`Arbi::swap_bytes()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let a = Arbi::from(0x12345678_u32);
    /// assert_eq!(a.swap_bytes_ref(), 0x78563412);
    /// ```
    pub fn swap_bytes_ref(&self) -> Self {
        let ret = self.clone();
        ret.swap_bytes()
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
            assert_eq!(digit_arbi.swap_bytes(), digit.swap_bytes() as u128);

            let ddigit = die_dd.sample(&mut rng);
            let ddigit_arbi = Arbi::from(ddigit);
            assert_eq!(ddigit_arbi.swap_bytes(), ddigit.swap_bytes() as u128);
        }
    }

    #[test]
    fn boundaries() {
        let zero = Arbi::zero();
        assert_eq!(zero.swap_bytes(), 0_u32.swap_bytes() as u128);

        let a = Arbi::from(Digit::MAX - 1);
        assert_eq!(a.swap_bytes(), (Digit::MAX - 1).swap_bytes() as u128);

        let a = Arbi::from(Digit::MAX);
        assert_eq!(a.swap_bytes(), Digit::MAX.swap_bytes() as u128);

        let a = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(
            a.clone().swap_bytes(),
            (Digit::MAX as DDigit + 1).swap_bytes() as u128
        );

        let a = Arbi::from(DDigit::MAX - 1);
        assert_eq!(a.swap_bytes(), (DDigit::MAX - 1).swap_bytes() as u128);

        let a = Arbi::from(DDigit::MAX);
        assert_eq!(a.swap_bytes(), DDigit::MAX.swap_bytes() as u128);
    }
}
