/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Utility to determine if a primitive integral type is signed or unsigned.

macro_rules! impl_is_signed {
    // Signed types (true)
    (signed: $($t:ty),*) => {
        $(
            impl IsSigned for $t {
                const IS_SIGNED: bool = true;

                fn is_signed() -> bool {
                    true
                }
            }
        )*
    };

    // Unsigned types (false)
    (unsigned: $($t:ty),*) => {
        $(
            impl IsSigned for $t {
                const IS_SIGNED: bool = false;

                fn is_signed() -> bool {
                    false
                }
            }
        )*
    };
}

#[allow(dead_code)]
pub(crate) trait IsSigned {
    const IS_SIGNED: bool;

    fn is_signed() -> bool;
}

impl_is_signed!(signed: i8, i16, i32, i64, i128, isize);
impl_is_signed!(unsigned: u8, u16, u32, u64, u128, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_signed_signed() {
        assert_eq!(i8::is_signed(), true);
        assert_eq!(i16::is_signed(), true);
        assert_eq!(i32::is_signed(), true);
        assert_eq!(i64::is_signed(), true);
        assert_eq!(i128::is_signed(), true);
        assert_eq!(isize::is_signed(), true);

        assert_eq!(i8::IS_SIGNED, true);
        assert_eq!(i16::IS_SIGNED, true);
        assert_eq!(i32::IS_SIGNED, true);
        assert_eq!(i64::IS_SIGNED, true);
        assert_eq!(i128::IS_SIGNED, true);
        assert_eq!(isize::IS_SIGNED, true);
    }

    #[test]
    fn test_is_signed_unsigned() {
        assert_eq!(u8::is_signed(), false);
        assert_eq!(u16::is_signed(), false);
        assert_eq!(u32::is_signed(), false);
        assert_eq!(u64::is_signed(), false);
        assert_eq!(u128::is_signed(), false);
        assert_eq!(usize::is_signed(), false);

        assert_eq!(u8::IS_SIGNED, false);
        assert_eq!(u16::IS_SIGNED, false);
        assert_eq!(u32::IS_SIGNED, false);
        assert_eq!(u64::IS_SIGNED, false);
        assert_eq!(u128::IS_SIGNED, false);
        assert_eq!(usize::IS_SIGNED, false);
    }
}
