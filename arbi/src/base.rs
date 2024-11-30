/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Defines a type used by [`Arbi::from_str_base()`] and
//! [`Arbi::to_string_base()`] for converting between strings and `Arbi`
//! integers.
//!
//! The [`Base`]  type encapsulates an integer in the range \\( [2, 36] \\), the
//! set of valid bases for converting between strings and [`Arbi`] integers.
//!
//! The [`Arbi::from_str_radix()`] and [`Arbi::to_string_radix()`] functions are
//! equivalent to their `_base` analogues, but panic in the event that the
//! provided `u32` radix argument is not in \\( [2, 36] \\).

#[allow(unused_imports)]
use crate::Arbi;
use core::fmt;

/// Stores an integer in the range [2, 36] (the set of valid bases for
/// converting between strings and [`Arbi`] integers).
///
/// # Examples
/// ```
/// use arbi::{Arbi, Base};
///
/// let b10 = Base::try_from(10).unwrap();
///
/// let a = Arbi::from(123456789);
///
/// let s = a.to_string_base(b10);
/// assert_eq!(s, "123456789");
///
/// let b = Arbi::from_str_base("-987654321", b10).unwrap();
/// assert_eq!(b, -987654321);
/// ```
#[derive(Debug, Copy, Clone)]
pub struct Base(pub(crate) u8);

/// Error that occurs when creating a new [`Base`].
///
/// # Examples
/// ```
/// use arbi::{Base, BaseError};
///
/// let b37 = Base::try_from(37);
/// assert!(matches!(b37, Err(BaseError::InvalidBase)));
/// ```
#[derive(Debug)]
pub enum BaseError {
    /// Base must be in the range \\( [2, 36] \\).
    InvalidBase,
}

impl fmt::Display for BaseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseError::InvalidBase => {
                write!(f, "Base must be in the range [2, 36]")
            }
        }
    }
}

impl core::error::Error for BaseError {}

impl TryFrom<u8> for Base {
    type Error = BaseError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if (2..=36).contains(&value) {
            Ok(Base(value))
        } else {
            Err(BaseError::InvalidBase)
        }
    }
}

impl From<Base> for u8 {
    fn from(value: Base) -> u8 {
        #[allow(clippy::useless_conversion)]
        value.value().into()
    }
}

impl From<Base> for u32 {
    fn from(value: Base) -> u32 {
        value.value().into()
    }
}

impl From<Base> for i32 {
    fn from(value: Base) -> i32 {
        value.value().into()
    }
}

impl TryFrom<usize> for Base {
    type Error = BaseError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        let as_u8: Result<u8, _> = value.try_into();

        match as_u8 {
            Err(_) => Err(BaseError::InvalidBase),
            Ok(the_u8) => the_u8.try_into(),
        }
    }
}

impl TryFrom<i32> for Base {
    type Error = BaseError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        let as_u8: Result<u8, _> = value.try_into();

        match as_u8 {
            Err(_) => Err(BaseError::InvalidBase),
            Ok(the_u8) => the_u8.try_into(),
        }
    }
}

impl TryFrom<u32> for Base {
    type Error = BaseError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        let as_u8: Result<u8, _> = value.try_into();

        match as_u8 {
            Err(_) => Err(BaseError::InvalidBase),
            Ok(the_u8) => the_u8.try_into(),
        }
    }
}

impl Base {
    /// Create a new [`Base`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Base;
    ///
    /// let b36 = Base::new(36).unwrap();
    /// ```
    pub fn new(value: u8) -> Result<Self, BaseError> {
        value.try_into()
    }

    /// Retrieve the underlying integer value.
    ///
    /// # Examples
    /// ```
    /// use arbi::Base;
    ///
    /// let b10 = Base::new(10).unwrap();
    /// assert_eq!(b10.value(), 10);
    /// ```
    pub fn value(self) -> u8 {
        self.0
    }
}

/// Base 10. Decimal.
pub const BASE10: Base = Base(10);

/// Base 10. Decimal.
pub const B10: Base = Base(10);

/// Base 2. Binary.
pub const BIN: Base = Base(2);

/// Base 8. Octal.
pub const OCT: Base = Base(8);

/// Base 10. Decimal.
pub const DEC: Base = Base(10);

/// Base 16. Hexadecimal.
pub const HEX: Base = Base(16);

/// Base 36. Hexatrigesimal.
pub const B36: Base = Base(36);
