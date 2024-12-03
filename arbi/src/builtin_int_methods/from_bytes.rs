/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::to_twos_complement::{ByteOrder, TwosComplement};
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
        let full_chunks = bytes.len() / DIGIT_BYTES;
        let remainder = bytes.len() % DIGIT_BYTES;
        let mut num = Arbi::with_capacity(
            full_chunks + if remainder > 0 { 1 } else { 0 },
        );
        for chunk in bytes.chunks_exact(DIGIT_BYTES) {
            let digit = Digit::from_le_bytes(chunk.try_into().unwrap());
            num.vec.push(digit);
        }
        if remainder > 0 {
            let mut last_bytes = [0u8; DIGIT_BYTES];
            last_bytes[..remainder]
                .copy_from_slice(&bytes[full_chunks * DIGIT_BYTES..]);
            let last_digit = Digit::from_le_bytes(last_bytes);
            num.vec.push(last_digit);
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
        if bytes.is_empty() {
            return Arbi::zero();
        }
        let full_chunks = bytes.len() / DIGIT_BYTES;
        let remainder = bytes.len() % DIGIT_BYTES;
        let mut num = Arbi::with_capacity(
            full_chunks + if remainder > 0 { 1 } else { 0 },
        );
        let full_chunks_iter = bytes.chunks_exact(DIGIT_BYTES);
        for chunk in full_chunks_iter.rev() {
            let digit = Digit::from_be_bytes(chunk.try_into().unwrap());
            num.vec.push(digit);
        }
        if remainder > 0 {
            let mut last_bytes = [0u8; DIGIT_BYTES];
            last_bytes[DIGIT_BYTES - remainder..]
                .copy_from_slice(&bytes[0..remainder]);
            let last_digit = Digit::from_be_bytes(last_bytes);
            num.vec.push(last_digit);
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
            num.vec.to_twos_complement(ByteOrder::Le);
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
    /// assert_eq!(value, i64::from_be_bytes(bytes));
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
        let mut num = Self::from_be_bytes(bytes);
        if is_negative {
            num.vec.to_twos_complement(ByteOrder::Le);
            num.neg = true;
        }
        num.trim();
        num
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate std;
    use crate::util::test::{get_seedable_rng, Rng};

    #[test]
    fn test_random_from_le_bytes_signed() {
        let (mut rng, _) = get_seedable_rng();

        // i64
        for _ in 0..i16::MAX {
            let mut bytes = [0u8; 8];
            rng.fill(&mut bytes);
            let expected_value = i64::from_le_bytes(bytes);
            let arbi_value = Arbi::from_le_bytes_signed(&bytes);
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
            let expected_value = i128::from_le_bytes(bytes);
            let arbi_value = Arbi::from_le_bytes_signed(&bytes);
            assert_eq!(
                arbi_value, expected_value,
                "Test failed for bytes: {:?}, arbi: {}",
                bytes, arbi_value
            );
        }
    }

    #[test]
    fn test_random_from_be_bytes_signed() {
        let (mut rng, _) = get_seedable_rng();

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
                "Test failed for bytes: {:?}, arbi: {}",
                bytes, arbi_value
            );
        }
    }
}
