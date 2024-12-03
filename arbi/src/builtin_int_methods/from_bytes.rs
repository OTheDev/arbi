/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

const DIGIT_BYTES: usize = core::mem::size_of::<Digit>();

impl Arbi {
    /// Creates an `Arbi` integer from its representation as a byte array
    /// in little endian, interpreted as a nonnegative integer.
    ///
    /// If `bytes` is empty, [`Arbi::zero()`] is returned.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let bytes = [0x78, 0x56, 0x34, 0x12, 0x34, 0x56, 0x78, 0x90];
    ///
    /// let value = Arbi::from_le_bytes(&bytes);
    /// assert_eq!(value, 0x9078563412345678_u64);
    /// assert_eq!(value, u64::from_le_bytes(bytes));
    ///
    /// let zero = Arbi::from_le_bytes(&[]);
    /// assert_eq!(zero, 0);
    /// ```
    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return Arbi::zero();
        }
        let mut num =
            Arbi::with_capacity((bytes.len() + DIGIT_BYTES - 1) / DIGIT_BYTES);
        let mut digit = 0;
        for (i, &byte) in bytes.iter().enumerate() {
            digit |= (byte as Digit) << ((i % DIGIT_BYTES) * 8);
            if i % DIGIT_BYTES == DIGIT_BYTES - 1 {
                num.vec.push(digit);
                digit = 0;
            }
        }
        if bytes.len() % DIGIT_BYTES != 0 {
            num.vec.push(digit);
        }
        num.trim();
        num
    }

    /// Creates an `Arbi` integer from its representation as a byte array
    /// in big endian, interpreted as a nonnegative integer.
    ///
    /// If `bytes` is empty, [`Arbi::zero()`] is returned.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let bytes = [0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78];
    ///
    /// let value = Arbi::from_be_bytes(&bytes);
    /// assert_eq!(value, 0x1234567812345678_u64);
    /// assert_eq!(value, u64::from_be_bytes(bytes));
    ///
    /// let zero = Arbi::from_be_bytes(&[]);
    /// assert_eq!(zero, 0);
    /// ```
    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        Self::from_be_bytes_reverse(bytes, true)
    }

    fn from_be_bytes_reverse(bytes: &[u8], reverse: bool) -> Self {
        if bytes.is_empty() {
            return Arbi::zero();
        }
        let mut num =
            Arbi::with_capacity((bytes.len() + DIGIT_BYTES - 1) / DIGIT_BYTES);
        let mut digit = 0;
        for (i, &byte) in bytes.iter().rev().enumerate() {
            digit |= (byte as Digit) << ((i % DIGIT_BYTES) * 8);
            if i % DIGIT_BYTES == DIGIT_BYTES - 1 {
                num.vec.push(digit);
                digit = 0;
            }
        }
        if bytes.len() % DIGIT_BYTES != 0 {
            num.vec.push(digit);
        }
        if reverse {
            num.vec.reverse();
        }
        num.trim();
        num
    }

    /// Creates an `Arbi` integer from its representation as a byte array
    /// in little endian, interpreted as a signed integer.
    ///
    /// If `bytes` is empty, [`Arbi::zero()`] is returned.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // Positive
    /// let bytes = [0x78, 0x56, 0x34, 0x12, 0x78, 0x56, 0x34, 0x12];
    /// let value = Arbi::from_le_bytes_signed(&bytes);
    /// assert_eq!(value, 0x1234567812345678_i64);
    /// assert_eq!(value, i64::from_le_bytes(bytes));
    ///
    /// // Negative
    /// let bytes = [0xb3, 0xb3, 0xb4, 0xb5, 0xb2, 0xb3, 0xb4, 0xb5];
    /// let value = Arbi::from_le_bytes_signed(&bytes);
    /// assert_eq!(value, i64::from_le_bytes(bytes));
    ///
    /// // Zero
    /// let bytes = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let value = Arbi::from_le_bytes_signed(&bytes);
    /// assert_eq!(value, 0);
    /// assert_eq!(value, i64::from_le_bytes(bytes));
    ///
    /// let zero = Arbi::from_le_bytes_signed(&[]);
    /// assert_eq!(zero, 0);
    /// ```
    pub fn from_le_bytes_signed(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return Arbi::zero();
        }
        let is_negative = bytes.last().map_or(false, |&b| b & 0x80 != 0);
        // TODO: one pass?
        let mut num = Self::from_le_bytes(bytes);
        if is_negative {
            Arbi::to_twos_complement_inplace(&mut num.vec);
            num.negate();
        }
        num.trim();
        num
    }

    /// Creates an `Arbi` integer from its representation as a byte array
    /// in big endian, interpreted as a signed integer.
    ///
    /// If `bytes` is empty, [`Arbi::zero()`] is returned.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// // Positive
    /// let bytes = [0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78];
    /// let value = Arbi::from_be_bytes_signed(&bytes);
    /// assert_eq!(value, 0x1234567812345678_i64);
    /// assert_eq!(value, i64::from_be_bytes(bytes));
    ///
    /// // Negative
    /// let bytes = [0xb5, 0xb4, 0xb3, 0xb2, 0xb5, 0xb4, 0xb3, 0xb3];
    /// let value = Arbi::from_be_bytes_signed(&bytes);
    /// assert_eq!(value, i64::from_be_bytes(bytes), "{}", value);
    ///
    /// // Zero
    /// let bytes = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    /// let value = Arbi::from_be_bytes_signed(&bytes);
    /// assert_eq!(value, 0);
    /// assert_eq!(value, i64::from_be_bytes(bytes));
    ///
    /// let zero = Arbi::from_be_bytes_signed(&[]);
    /// assert_eq!(zero, 0);
    /// ```
    pub fn from_be_bytes_signed(bytes: &[u8]) -> Self {
        if bytes.is_empty() {
            return Arbi::zero();
        }
        let is_negative = bytes[0] & 0x80 != 0;
        // TODO: one pass?
        let mut num = Self::from_be_bytes_reverse(bytes, false);
        if is_negative {
            Arbi::to_twos_complement_inplace(&mut num.vec);
            num.neg = true;
        }
        num.trim();
        num
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};
    extern crate std;

    #[test]
    fn test_random_from_le_bytes_signed() {
        let mut rng = thread_rng();

        // i64
        for _ in 0..i16::MAX {
            let mut bytes = [0u8; 8];
            rng.fill(&mut bytes);
            let expected_value = i64::from_le_bytes(bytes);
            let arbi_value = Arbi::from_le_bytes_signed(&bytes);
            assert_eq!(
                arbi_value, expected_value,
                "Test failed for bytes: {:?}",
                bytes
            );
        }

        // i128
        for _ in 0..i16::MAX {
            let mut bytes = [0u8; 16];
            rng.fill(&mut bytes);
            let expected_value = i128::from_le_bytes(bytes);
            let arbi_value = Arbi::from_le_bytes_signed(&bytes);
            assert_eq!(
                arbi_value, expected_value,
                "Test failed for bytes: {:?}",
                bytes
            );
        }
    }

    #[test]
    fn test_random_from_be_bytes_signed() {
        let mut rng = thread_rng();

        // i64
        for _ in 0..i16::MAX {
            let mut bytes = [0u8; 8];
            rng.fill(&mut bytes);
            let arbi_value = Arbi::from_be_bytes_signed(&bytes);
            let expected_value = i64::from_be_bytes(bytes);
            assert_eq!(
                arbi_value, expected_value,
                "Test failed for bytes: {:?}, arbi: {}",
                bytes, arbi_value
            );
        }

        // i128
        for _ in 0..i16::MAX {
            let mut bytes = [0u8; 16];
            rng.fill(&mut bytes);
            let arbi_value = Arbi::from_be_bytes_signed(&bytes);
            let expected_value = i128::from_be_bytes(bytes);
            assert_eq!(
                arbi_value, expected_value,
                "Test failed for bytes: {:?}",
                bytes
            );
        }
    }
}
