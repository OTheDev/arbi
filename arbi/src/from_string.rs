/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Base;
use crate::{Arbi, Digit};
use core::fmt;
use core::str::FromStr;

/// Errors that occur when parsing a string into an [`Arbi`].
///
/// Valid strings may optionally consist of a single leading + or - sign (no
/// sign suggests nonnegative), followed by a mandatory nonempty string of
/// base-`base` digits, where `base` must represent an integer in
/// \\( [2, 36] \\).
///
/// The requirements are designed to be consistent with the behavior of
/// `from_str_radix()` for primitive integer types. For example, see
/// [`i32::from_str_radix()`].
///
/// # Examples
/// ```
/// use arbi::{Arbi, ParseError};
/// let a = Arbi::from_str_radix("-123456789", 10).unwrap();
/// assert_eq!(a, -123456789);
/// let b = Arbi::from_str_radix("-12345a6789", 10);
/// assert!(matches!(b, Err(ParseError::InvalidDigit)));
/// let c = Arbi::from_str_radix("  -   ", 10);
/// assert!(matches!(c, Err(ParseError::InvalidDigit)));
/// let d = Arbi::from_str_radix("", 10);
/// assert!(matches!(d, Err(ParseError::Empty)));
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    /// Invalid digit found for the provided base.
    InvalidDigit,
    /// The provided string is empty.
    Empty,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDigit => {
                write!(f, "Invalid digit found for the provided base")
            }
            Self::Empty => {
                write!(f, "The provided string is empty")
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

#[cfg(feature = "std")]
#[cfg(test)]
mod std_tests {
    use super::ParseError;
    use std::error::Error;

    #[test]
    fn test_error_trait() {
        let err: ParseError = ParseError::InvalidDigit;
        assert!(err.source().is_none());
    }
}

/// Calculate base ** exp
const fn pow(base: Digit, exp: usize) -> Digit {
    // (0..exp).fold(1, |acc, _| acc * base)
    let mut result = 1;
    let mut i = 0;
    while i < exp {
        result *= base;
        i += 1;
    }
    result
}

#[derive(Copy, Clone)]
pub(crate) struct BaseMbs {
    // max batch size
    pub(crate) mbs: usize,
    // base ** mbs
    pub(crate) base_pow_mbs: Digit,
}

/// Configuration for mappings and batch sizes
pub(crate) mod configs {
    use super::{pow, BaseMbs, Digit};
    use crate::DDigit;

    pub(crate) const BASE_MBS: [BaseMbs; 37] = compute_base_mbs();

    // For example, if digit <==> uint32_t (uint64_t), 10^{9} (10^{19}) is the
    // highest power of 10 that fits in it.
    const fn compute_base_mbs() -> [BaseMbs; 37] {
        let mut base_mbs = [BaseMbs {
            mbs: 0,
            base_pow_mbs: 0,
        }; 37];
        let mut base = 2;
        while base <= 36 {
            // Calculate max batch size
            let mut max_batch_size = 0;
            let mut b = base as DDigit;
            while b < Digit::MAX as DDigit {
                b *= base as DDigit;
                max_batch_size += 1;
            }

            base_mbs[base] = BaseMbs {
                mbs: max_batch_size,
                base_pow_mbs: pow(base as Digit, max_batch_size),
            };
            base += 1;
        }
        base_mbs
    }
}

impl Arbi {
    /// Equivalent to [`Arbi::from_str_base()`], but panics if the base is
    /// invalid (i.e. not in \\( [2, 36] \\)).
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Base};
    /// let x = Arbi::from_str_radix("987654321", 10).unwrap();
    /// assert_eq!(x, 987654321);
    pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseError> {
        let base: Base = match radix.try_into() {
            Err(_) => panic!("`radix` is not an integer in [2, 36]"),
            Ok(b) => b,
        };

        Arbi::from_str_base(src, base)
    }

    /// Construct an integer from a string representing a base-`base` integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::{base::DEC, Arbi};
    /// let x = Arbi::from_str_base("987654321", DEC).unwrap();
    /// assert_eq!(x, 987654321);
    /// ```
    pub fn from_str_base(s: &str, base: Base) -> Result<Self, ParseError> {
        let mut res = Self::new();
        res.assign_str_base(s, base)?;
        Ok(res)
    }
}

/* TODO: clean up */

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BaseError;
    use alloc::string::{String, ToString};

    #[test]
    fn test_from_str_base_invalid_base() {
        for (_, base) in &[("0", 0), ("0", 1), ("0", 37)] {
            assert!(matches!(
                Base::try_from(*base),
                Err(BaseError::InvalidBase)
            ));
        }
    }

    #[test]
    fn test_parse_error() {
        assert!(matches!(
            Arbi::from_str_base("", 10.try_into().unwrap()),
            Err(ParseError::Empty)
        ));
        assert!(matches!(
            Arbi::from_str_base("        ", 10.try_into().unwrap()),
            Err(ParseError::InvalidDigit)
        ));
        for s in &["  -", "      -"] {
            assert!(matches!(
                Arbi::from_str_base(s, 10.try_into().unwrap()),
                Err(ParseError::InvalidDigit)
            ));
        }
    }

    #[test]
    fn test_parse_error_invalid_digit() {
        assert!(matches!(
            Arbi::from_str_radix("-00A1", 2),
            Err(ParseError::InvalidDigit)
        ));
    }

    #[test]
    fn test_from_str_base_small_strings() {
        for (s, expected) in &[
            ("0", 0),
            ("-0", 0),
            ("+0", 0),
            ("987", 987),
            ("-987", -987),
            ("+987", 987),
            ("+00100", 100),
            ("+000000", 0),
            ("18446744073709551615", 18446744073709551615_i128),
        ] {
            let arbi = Arbi::from_str_base(s, 10.try_into().unwrap()).unwrap();
            assert_eq!(arbi, *expected);
        }
    }

    #[cfg(not(target_pointer_width = "64"))]
    fn test_construct_from_string(base: Base) {
        use crate::to_string::tests::ToStringBase;
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };
        use crate::{DDigit, SDDigit, SDigit};

        for x in [
            0 as SDDigit,
            Digit::MAX as SDDigit,
            DDigit::MAX as SDDigit,
            SDigit::MIN as SDDigit,
            SDDigit::MIN as SDDigit,
            SDigit::MAX as SDDigit,
            SDDigit::MAX as SDDigit,
            SQDigit::MIN,
            SQDigit::MAX,
        ] {
            assert_eq!(
                Arbi::from_str_base(&x.to_string_base(base), base).unwrap(),
                x,
            );
        }

        assert_eq!(
            Arbi::from_str_base(&QDigit::MAX.to_string_base(base), base)
                .unwrap(),
            QDigit::MAX
        );

        let (mut rng, _) = get_seedable_rng();

        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_16 = get_uniform_die(i16::MIN, i16::MAX);
        for _ in 0..i16::MAX {
            let rv = die.sample(&mut rng);
            let s = rv.to_string_base(base);
            assert_eq!(Arbi::from_str_base(&s, base).unwrap(), rv);

            let rv_16 = die_16.sample(&mut rng);
            let s = rv_16.to_string_base(base);
            assert_eq!(Arbi::from_str_base(&s, base).unwrap(), rv_16);
        }
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn test_construct_from_string_() {
        for i in 2..=36 {
            test_construct_from_string(i.try_into().unwrap());
        }
    }

    #[test]
    fn test_from_str_base_large_string() {
        use crate::base::DEC;

        let mut s: String = "\
            9999090900932323293029323092309309232309920940294242043232099290329\
            3029320312904092384092384903840928490320948239048903284920139402030\
            2309402934092304904902394029340932049302942313094874981748920028034\
            3298980495840298502480239483390099999029100293809809809809099923420\
        "
        .into();

        assert_eq!(Arbi::from_str_base(&s, DEC).unwrap().to_string(), s);

        s.insert(0, '-');
        let a = Arbi::from_str_base(&s, DEC).unwrap();
        assert!(a.is_negative());
        assert_eq!(a.to_string(), s);
    }

    #[test]
    fn test_from_str_radix() {
        let a = Arbi::from_str_radix("-987654321", 10).unwrap();
        assert_eq!(a, -987654321);

        let b =
            Arbi::from_str_radix("10001101001111000000111000010101011011", 2)
                .unwrap();
        assert_eq!(b, 151649486171_i64);
    }

    #[test]
    fn test_from_str() {
        let a = Arbi::from_str("-987654321").unwrap();
        assert_eq!(a, -987654321);
    }

    #[test]
    fn test_str_parse() {
        let a: Arbi = "-987654321".parse().unwrap();
        assert_eq!(a, -987654321);

        let a = "123456789".parse::<Arbi>().unwrap();
        assert_eq!(a, 123456789);

        assert!(matches!(
            "12A456789".parse::<Arbi>(),
            Err(ParseError::InvalidDigit)
        ));
        assert!(matches!(
            "   -".parse::<Arbi>(),
            Err(ParseError::InvalidDigit)
        ));

        let a = "\
            123456789012345678901234567890123456789043909809801329009092930\
        ";
        assert_eq!(a.parse::<Arbi>().unwrap().to_string(), a);

        let a = "\
            -12345678901234567890123456789012345678909098909809802340982349\
        ";
        assert_eq!(a.parse::<Arbi>().unwrap().to_string(), a);

        assert_eq!("0".parse::<Arbi>().unwrap(), 0);
    }
}

impl FromStr for Arbi {
    type Err = ParseError;

    /// Equivalent to [`Arbi::from_str_radix()`] with base 10.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// use core::str::FromStr;
    /// let a = Arbi::from_str("-987654321").unwrap();
    /// assert_eq!(a, -987654321);
    /// let b = "123456789".parse::<Arbi>().unwrap();
    /// assert_eq!(b, 123456789);
    /// ```
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Arbi::from_str_radix(src, 10)
    }
}
