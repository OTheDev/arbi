/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

#[allow(dead_code)]
pub(crate) const fn max_digits<T>() -> usize {
    use crate::uints::div_ceil_usize;
    use crate::Digit;

    div_ceil_usize(
        core::mem::size_of::<T>().checked_mul(8).unwrap(),
        Digit::BITS as usize,
    )
}

#[cfg(test)]
mod test_max_digits {
    use super::max_digits;
    use crate::Digit;

    #[test]
    fn test_max_digits() {
        if Digit::BITS == 32 {
            assert_eq!(max_digits::<i8>(), 1);
            assert_eq!(max_digits::<i16>(), 1);
            assert_eq!(max_digits::<i32>(), 1);
            assert_eq!(max_digits::<i64>(), 2);
            assert_eq!(max_digits::<i128>(), 4);

            assert_eq!(max_digits::<u8>(), 1);
            assert_eq!(max_digits::<u16>(), 1);
            assert_eq!(max_digits::<u32>(), 1);
            assert_eq!(max_digits::<u64>(), 2);
            assert_eq!(max_digits::<u128>(), 4);
        } else if Digit::BITS == 64 {
            assert_eq!(max_digits::<i8>(), 1);
            assert_eq!(max_digits::<i16>(), 1);
            assert_eq!(max_digits::<i32>(), 1);
            assert_eq!(max_digits::<i64>(), 1);
            assert_eq!(max_digits::<i128>(), 2);

            assert_eq!(max_digits::<u8>(), 1);
            assert_eq!(max_digits::<u16>(), 1);
            assert_eq!(max_digits::<u32>(), 1);
            assert_eq!(max_digits::<u64>(), 1);
            assert_eq!(max_digits::<u128>(), 2);
        }
    }
}
