/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::Base;
use crate::{Arbi, Digit};
use core::fmt;
use core::str::FromStr;

/// Errors that occur when parsing a string into an [`Arbi`].
///
/// # Examples
/// ```
/// use arbi::{Arbi, ParseError};
///
/// let a = Arbi::from_str_radix("-123456789", 10).unwrap();
/// assert_eq!(a, -123456789);
///
/// let b = Arbi::from_str_radix("-12345a6789", 10);
/// assert!(matches!(b, Err(ParseError::InvalidDigit)));
///
/// let c = Arbi::from_str_radix("  -   ", 10);
/// assert!(matches!(c, Err(ParseError::Empty)));
/// ```
#[derive(Debug, PartialEq)]
pub enum ParseError {
    /// Invalid digit found for the provided base.
    InvalidDigit,

    /// The provided string is empty (after stripping outer whitespace) or no
    /// valid digits for the provided base were found.
    Empty,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDigit => {
                write!(f, "Invalid digit found for the provided base")
            }
            Self::Empty => {
                write!(f, "The provided string is empty (after stripping outer whitespace) or no valid digits for the provided base were found")
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

    pub(crate) const CHAR_TO_B36_MAP: [u8; 256] = create_char_to_b36_map();
    pub(crate) const N_DIGITS: usize = 10;
    pub(crate) const N_LETTERS: usize = 26;
    pub(crate) const LOWERCASE: [u8; N_LETTERS] = [
        b'a', b'b', b'c', b'd', b'e', b'f', b'g', b'h', b'i', b'j', b'k', b'l',
        b'm', b'n', b'o', b'p', b'q', b'r', b's', b't', b'u', b'v', b'w', b'x',
        b'y', b'z',
    ];
    pub(crate) const UPPERCASE: [u8; N_LETTERS] = [
        b'A', b'B', b'C', b'D', b'E', b'F', b'G', b'H', b'I', b'J', b'K', b'L',
        b'M', b'N', b'O', b'P', b'Q', b'R', b'S', b'T', b'U', b'V', b'W', b'X',
        b'Y', b'Z',
    ];

    const fn create_char_to_b36_map() -> [u8; 256] {
        let mut map = [0xFF; 256];
        let mut i = 0;
        while i < N_DIGITS {
            map[(b'0' + i as u8) as usize] = i as u8;
            i += 1;
        }
        let mut j: usize = 0;
        while j < N_LETTERS {
            map[LOWERCASE[j] as usize] = (10 + j) as u8;
            map[UPPERCASE[j] as usize] = (10 + j) as u8;
            j += 1;
        }
        map
    }

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
    pub(crate) fn from_str_base_(
        s: &str,
        base: Base,
    ) -> Result<Self, ParseError> {
        let base = base.value() as u32;

        // Allow leading and trailing whitespace
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err(ParseError::Empty);
        }

        let mut x = Arbi::new();

        // Allow plus/minus sign to precede first base-`base` digit
        let mut chars = trimmed.chars();
        if let Some(first_char) = chars.next() {
            match first_char {
                '-' => x.neg = true,
                '+' => x.neg = false,
                _ => chars = trimmed.chars(),
            }
        }

        let start_digit =
            chars.clone().take_while(|ch| ch.is_ascii_alphanumeric());
        let n_base = start_digit.clone().count();

        if n_base == 0 {
            return Err(ParseError::Empty);
        }

        let base_idx = base as usize;
        let BaseMbs { mbs, base_pow_mbs } = configs::BASE_MBS[base_idx];

        x.vec.reserve(usize::div_ceil_(n_base, mbs));

        let mut dec_iter = start_digit.clone();
        let rem_batch_size = n_base % mbs;

        // Initialize batch value
        let mut batch = 0;
        // Convert batch substring to integer value
        for _ in 0..rem_batch_size {
            if let Some(ch) = dec_iter.next() {
                let char_value = configs::CHAR_TO_B36_MAP[ch as usize] as Digit;
                if char_value == 0xFF || char_value >= base {
                    return Err(ParseError::InvalidDigit);
                }
                batch = char_value + batch * base;
            }
        }

        // x is initially zero, so multiplication is zero in imul1add1()
        if batch != 0 {
            x.vec.push(batch);
        }

        for _ in 0..(n_base / mbs) {
            // Initialize batch value
            batch = 0;
            // Convert batch substring to integer value
            for _ in 0..mbs {
                if let Some(ch) = dec_iter.next() {
                    let char_value =
                        configs::CHAR_TO_B36_MAP[ch as usize] as Digit;
                    if char_value == 0xFF || char_value >= base {
                        return Err(ParseError::InvalidDigit);
                    }
                    batch = char_value + batch * base;
                } else {
                    break;
                }
            }
            Self::imul1add1(&mut x, base_pow_mbs, Some(batch));
        }

        x.trim();
        Ok(x)
    }

    /// Equivalent to [`Arbi::from_str_base()`], but panics if the base is
    /// invalid (i.e. not in \\( [2, 36] \\)).
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Base};
    ///
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
    /// Allows leading whitespace and/or a plus/minus sign before the first
    /// base-`base` digit. `base` must be an integer in \\( [2, 36] \\).
    /// Trailing whitespace is ignored.
    ///
    /// # Examples
    /// ```
    /// use arbi::{base::DEC, Arbi};
    ///
    /// let x = Arbi::from_str_base("987654321", DEC).unwrap();
    /// assert_eq!(x, 987654321);
    /// ```
    pub fn from_str_base(s: &str, base: Base) -> Result<Self, ParseError> {
        // let mut ret = Arbi::zero();
        // match ret.from_str_base_inplace(s, base) {
        //     Ok(_) => Ok(ret),
        //     Err(e) => Err(e),
        // }

        // TODO: maybe just use inplace?
        Self::from_str_base_(s, base)
    }

    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn from_str_base_inplace(
        &mut self,
        s: &str,
        base: Base,
    ) -> Result<(), ParseError> {
        let base = base.value() as u32;

        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err(ParseError::Empty);
        }

        let mut chars = trimmed.chars();
        let mut is_negative = false;

        if let Some(first_char) = chars.next() {
            match first_char {
                '-' => is_negative = true,
                '+' => (),
                _ => chars = trimmed.chars(),
            }
        }

        // First Pass: Validation
        let mut n_base = 0;
        for ch in chars.clone() {
            let char_value = configs::CHAR_TO_B36_MAP[ch as usize];
            if char_value == 0xFF || char_value as u32 >= base {
                return Err(ParseError::InvalidDigit);
            }
            n_base += 1;
        }

        if n_base == 0 {
            return Err(ParseError::Empty);
        }

        let start_digit = chars.clone().take_while(|&ch| {
            let char_value = configs::CHAR_TO_B36_MAP[ch as usize];
            !(char_value == 0xFF || char_value as u32 >= base)
        });

        // Second Pass: Modification
        let base_idx = base as usize;
        let BaseMbs { mbs, base_pow_mbs } = configs::BASE_MBS[base_idx];
        let estimate = usize::div_ceil_(n_base, mbs);

        if self.vec.capacity() < estimate {
            self.vec.reserve(estimate - self.vec.capacity());
        }
        self.vec.clear();
        self.neg = is_negative;

        let mut dec_iter = start_digit.clone();
        let rem_batch_size = n_base % mbs;

        // Initialize batch value
        let mut batch = 0;
        // Convert batch substring to integer value
        for _ in 0..rem_batch_size {
            if let Some(ch) = dec_iter.next() {
                let char_value = configs::CHAR_TO_B36_MAP[ch as usize] as Digit;
                batch = char_value + batch * base;
            }
        }

        // x is initially zero, so multiplication is zero in imul1add1()
        if batch != 0 {
            self.vec.push(batch);
        }

        for _ in 0..(n_base / mbs) {
            // Initialize batch value
            batch = 0;
            // Convert batch substring to integer value
            for _ in 0..mbs {
                if let Some(ch) = dec_iter.next() {
                    let char_value =
                        configs::CHAR_TO_B36_MAP[ch as usize] as Digit;
                    batch = char_value + batch * base;
                } else {
                    break;
                }
            }
            Self::imul1add1(self, base_pow_mbs, Some(batch));
        }

        self.trim();
        Ok(())
    }
}

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
    fn test_parse_error_empty() {
        assert!(matches!(
            Arbi::from_str_base("", 10.try_into().unwrap()),
            Err(ParseError::Empty)
        ));

        assert!(matches!(
            Arbi::from_str_base("        ", 10.try_into().unwrap()),
            Err(ParseError::Empty)
        ));

        for s in &["  -", "      -"] {
            assert!(matches!(
                Arbi::from_str_base(s, 10.try_into().unwrap()),
                Err(ParseError::Empty)
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
            ("     0 ", 0),
            ("      -0", 0),
            ("987", 987),
            ("-987", -987),
            ("+987", 987),
            ("  -987", -987),
            ("+00100", 100),
            ("+000000", 0),
            ("    00009876", 9876),
            ("18446744073709551615", 18446744073709551615_i128),
        ] {
            let arbi = Arbi::from_str_base(s, 10.try_into().unwrap()).unwrap();
            assert_eq!(arbi, *expected);
        }
    }

    fn test_construct_from_string(base: Base) {
        use crate::to_string::tests::ToStringBase;
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };
        use crate::{DDigit, QDigit, SDDigit, SDigit, SQDigit};

        for x in [
            0 as SQDigit,
            Digit::MAX as SQDigit,
            DDigit::MAX as SQDigit,
            SDigit::MIN as SQDigit,
            SDDigit::MIN as SQDigit,
            SDigit::MAX as SQDigit,
            SDDigit::MAX as SQDigit,
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

        let die = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
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
        assert!(matches!("   -".parse::<Arbi>(), Err(ParseError::Empty)));

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

    /// Uses [`Arbi::from_str_radix()`] with base 10.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// use core::str::FromStr;
    ///
    /// let a = Arbi::from_str("-987654321").unwrap();
    /// assert_eq!(a, -987654321);
    ///
    /// let b = "123456789".parse::<Arbi>().unwrap();
    /// assert_eq!(b, 123456789);
    /// ```
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Arbi::from_str_radix(src, 10)
    }
}
