/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::to_twos_complement::{ByteOrder, TwosComplement};
use crate::Arbi;
use alloc::vec::Vec;

impl Arbi {
    /// Returns the memory representation of this integer as a byte [`Vec`] in
    /// little-endian byte order, interpreted as a nonnegative integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::from(0x1234567890123456_u64);
    ///
    /// let bytes = a.to_le_bytes();
    /// assert_eq!(bytes, [0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12]);
    /// assert_eq!(bytes, 0x1234567890123456_u64.to_le_bytes());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn to_le_bytes(&self) -> Vec<u8> {
        self.vec
            .iter()
            .flat_map(|digit| digit.to_le_bytes())
            .collect()
    }

    /// Returns the memory representation of this integer as a byte [`Vec`] in
    /// big-endian (network) byte order, interpreted as a nonnegative integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::from(0x1234567890123456_u64);
    ///
    /// let bytes = a.to_be_bytes();
    /// assert_eq!(bytes, [0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56]);
    /// assert_eq!(bytes, 0x1234567890123456_u64.to_be_bytes());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn to_be_bytes(&self) -> Vec<u8> {
        self.vec
            .iter()
            .rev()
            .flat_map(|digit| digit.to_be_bytes())
            .collect()
    }

    /// Returns the memory representation of this integer as a byte [`Vec`] in
    /// little-endian byte order, interpreted as a signed integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::from(-0x1234567890123456_i64);
    ///
    /// let bytes = a.to_le_bytes_signed();
    /// assert_eq!(bytes, (-0x1234567890123456_i64).to_le_bytes());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn to_le_bytes_signed(&self) -> Vec<u8> {
        let mut result = self.to_le_bytes();
        if self.neg {
            result.to_twos_complement(ByteOrder::Le);
        }
        result
    }

    /// Returns the memory representation of this integer as a byte [`Vec`] in
    /// big-endian (network) byte order, interpreted as a signed integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::from(-0x1234567890123456_i64);
    ///
    /// let bytes = a.to_be_bytes_signed();
    /// assert_eq!(bytes, (-0x1234567890123456_i64).to_be_bytes());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    pub fn to_be_bytes_signed(&self) -> Vec<u8> {
        let mut result = self.to_be_bytes();
        if self.neg {
            result.to_twos_complement(ByteOrder::Be);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate std;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Digit, SDigit};

    macro_rules! test_conv {
        ($rng:expr, $die:expr, $signed:ident) => {{
            for _ in 0..i16::MAX {
                let r = $die.sample($rng);
                let a = Arbi::from(r);

                if $signed {
                    assert_eq!(
                        r.to_le_bytes(),
                        a.to_le_bytes_signed().as_ref()
                    );
                    assert_eq!(
                        r.to_be_bytes(),
                        a.to_be_bytes_signed().as_ref()
                    );
                } else {
                    assert_eq!(r.to_le_bytes(), a.to_le_bytes().as_ref());
                    assert_eq!(r.to_be_bytes(), a.to_be_bytes().as_ref());
                }
            }
        }};
    }

    #[test]
    fn test_random_to_le_and_be_bytes_unsigned() {
        let (mut rng, _) = get_seedable_rng();
        let die_i64 = get_uniform_die(i64::MIN, i64::MAX);
        let die_i128 = get_uniform_die(i128::MIN, i128::MAX);
        let die_u64 = get_uniform_die(u64::MIN, u64::MAX);
        let die_u128 = get_uniform_die(u128::MIN, u128::MAX);
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);

        test_conv!(&mut rng, die_i64, true);
        test_conv!(&mut rng, die_i128, true);
        test_conv!(&mut rng, die_sdigit, true);
        test_conv!(&mut rng, die_u64, false);
        test_conv!(&mut rng, die_u128, false);
        test_conv!(&mut rng, die_digit, false);
    }
}
