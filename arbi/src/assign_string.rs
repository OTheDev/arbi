/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::from_string::{configs::BASE_MBS, BaseMbs, ParseError};
use crate::uints::UnsignedUtilities;
use crate::Base;
use crate::{Arbi, Digit};

impl Arbi {
    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
    ///
    /// <div class="warning">
    ///
    /// If a parsing error is returned, `self`'s value may be different from its
    /// original.
    ///
    /// </div>
    ///
    /// # Panic
    /// Panics if `radix` is not in \\( [2, 36] \\). Use
    /// [`Arbi::assign_str_base`] for a panic-free version.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, ParseError};
    ///
    /// let mut x = Arbi::with_capacity(10);
    /// assert_eq!(x, 0);
    ///
    /// match x.assign_str_radix("123456789", 10) {
    ///     Ok(_) => assert_eq!(x, 123456789),
    ///     Err(e) => match e {
    ///         ParseError::InvalidDigit => panic!("invalid digit"),
    ///         ParseError::Empty => panic!("empty string"),
    ///     },
    /// }
    ///
    /// x.assign_str_radix("7c2ecdfacad74e0f0101b", 16).unwrap();
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// Panics on invalid `radix` values
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut x = Arbi::with_capacity(5);
    /// x.assign_str_radix("7c2ecdfacad74e0f0101b", 37);
    /// ```
    ///
    /// Example invalid strings
    /// ```
    /// use arbi::{Arbi, ParseError};
    ///
    /// let mut a = Arbi::zero();
    ///
    /// assert!(matches!(a.assign_str_radix("", 10), Err(ParseError::Empty)));
    /// assert!(matches!(
    ///     a.assign_str_radix("   - ", 10),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// assert!(matches!(
    ///     a.assign_str_radix("ffff", 10),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// ```
    pub fn assign_str_radix(
        &mut self,
        s: &str,
        radix: u32,
    ) -> Result<(), ParseError> {
        let base = match Base::try_from(radix) {
            Ok(b) => b,
            Err(_) => panic!("Invalid radix {}", radix),
        };
        self.assign_str_base(s, base)
    }

    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
    ///
    /// <div class="warning">
    ///
    /// If a parsing error is returned, `self`'s value may be different from its
    /// original.
    ///
    /// </div>
    ///
    /// # Examples
    /// ```
    /// use arbi::{
    ///     base::{DEC, HEX},
    ///     Arbi, ParseError,
    /// };
    ///
    /// let mut x = Arbi::with_capacity(10);
    /// assert_eq!(x, 0);
    ///
    /// match x.assign_str_base("123456789", DEC) {
    ///     Ok(_) => assert_eq!(x, 123456789),
    ///     Err(e) => match e {
    ///         ParseError::InvalidDigit => panic!("invalid digit"),
    ///         ParseError::Empty => panic!("empty string"),
    ///     },
    /// }
    ///
    /// x.assign_str_base("7c2ecdfacad74e0f0101b", HEX).unwrap();
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// Example invalid strings:
    /// ```
    /// use arbi::{base::DEC, Arbi, ParseError};
    ///
    /// let mut a = Arbi::zero();
    ///
    /// assert!(matches!(a.assign_str_base("", DEC), Err(ParseError::Empty)));
    /// assert!(matches!(
    ///     a.assign_str_base("   - ", DEC),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// assert!(matches!(
    ///     a.assign_str_base("ffff", DEC),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// ```
    pub fn assign_str_base(
        &mut self,
        s: &str,
        base: Base,
    ) -> Result<(), ParseError> {
        let (base_digits, has_minus_sign) =
            Self::parse_str_sign_skip_leading_zeros(s)?;
        if base_digits.is_empty() {
            self.make_zero();
            return Ok(());
        }

        // Get configuration for this base
        let base_val = base.value() as u32;
        let BaseMbs { mbs, base_pow_mbs } = BASE_MBS[base_val as usize];

        // Reserve estimated capacity
        let estimate = usize::div_ceil_(base_digits.len(), mbs);
        self.vec
            .reserve(estimate.saturating_sub(self.vec.capacity()));
        self.vec.clear();
        self.neg = has_minus_sign;

        #[cfg(debug_assertions)]
        let initial_capacity = self.vec.capacity();

        let n_base = base_digits.len();
        let rem_batch_size = n_base % mbs;
        let mut pos = 0;

        /* Handle first partial chunk */
        if rem_batch_size > 0 {
            // Initialize batch value
            let mut batch: Digit = 0;
            // Convert batch substring to integer value
            let end = pos + rem_batch_size;
            while pos < end {
                match (base_digits[pos] as char).to_digit(base_val) {
                    Some(digit) => {
                        batch = digit + batch * base_val;
                        pos += 1;
                    }
                    None => return Err(ParseError::InvalidDigit),
                }
            }
            debug_assert!(batch != 0);
            self.vec.push(batch);
        }

        /* Process remaining full-size chunks */
        while pos < n_base {
            // Initialize batch value
            let mut batch: Digit = 0;
            // Convert batch substring to integer value
            let end = pos + mbs;
            while pos < end {
                match (base_digits[pos] as char).to_digit(base_val) {
                    Some(digit) => {
                        batch = digit + batch * base_val;
                        pos += 1;
                    }
                    None => return Err(ParseError::InvalidDigit),
                }
            }
            Self::imul1add1(self, base_pow_mbs, Some(batch));
        }

        #[cfg(debug_assertions)]
        debug_assert_eq!(self.vec.capacity(), initial_capacity);

        self.trim();
        Ok(())
    }

    pub(crate) fn parse_str_sign(s: &str) -> Result<(&[u8], bool), ParseError> {
        if s.is_empty() {
            return Err(ParseError::Empty);
        }

        let s = s.as_bytes();

        let (base_digits, has_minus_sign) = match s {
            [b'-' | b'+'] => {
                return Err(ParseError::InvalidDigit);
            }
            [b'-', rest @ ..] => (rest, true),
            [b'+', rest @ ..] => (rest, false),
            _ => (s, false),
        };
        debug_assert!(!base_digits.is_empty());

        Ok((base_digits, has_minus_sign))
    }

    pub(crate) fn parse_str_sign_skip_leading_zeros(
        s: &str,
    ) -> Result<(&[u8], bool), ParseError> {
        let (mut base_digits, has_minus_sign) = Self::parse_str_sign(s)?;
        while let [c, rest @ ..] = base_digits {
            if *c != b'0' {
                break;
            }
            base_digits = rest;
        }
        Ok((base_digits, has_minus_sign))
    }

    #[allow(dead_code)]
    pub(crate) fn validate_str_base(
        s: &str,
        base: Base,
    ) -> Result<(&[u8], bool), ParseError> {
        let (mut base_digits, has_minus_sign) = Self::parse_str_sign(s)?;

        let base: u32 = base.value() as u32;

        while let [c, rest @ ..] = base_digits {
            let _ = match (*c as char).to_digit(base) {
                Some(value) => value,
                None => {
                    return Err(ParseError::InvalidDigit);
                }
            };

            base_digits = rest;
        }

        Ok((base_digits, has_minus_sign))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::DEC;
    use crate::{
        util::test::{get_seedable_rng, get_uniform_die, Distribution},
        DDigit, SDDigit,
    };
    use alloc::string::{String, ToString};

    #[test]
    fn test_assign_str_base() {
        let mut x = Arbi::zero();

        x.assign_str_base("0", DEC).unwrap();
        assert_eq!(&x, 0);

        x.assign_str_base("3239", DEC).unwrap();
        assert_eq!(&x, 3239);

        x.assign_str_base("-3239", DEC).unwrap();
        assert_eq!(&x, -3239);
    }

    #[test]
    #[should_panic]
    fn assign_str_base_empty_string() {
        let mut x = Arbi::zero();
        x.assign_str_base("", DEC).unwrap();
    }

    #[test]
    #[should_panic]
    fn assign_str_base_from_bad_string() {
        let mut x = Arbi::zero();
        x.assign_str_base("  -", DEC).unwrap();
    }

    #[test]
    fn misc() {
        let mut x = Arbi::zero();
        let s = "999909090093232329302932309230930923230992094029424204";
        let u = "-999909090093232329302932309230930923230992094029424204";

        x.assign_str_base(s, DEC).unwrap();
        assert_eq!(x.to_string_base(10.try_into().unwrap()), s);

        x.assign_str_base(u, DEC).unwrap();
        assert_eq!(x.to_string_base(10.try_into().unwrap()), u);

        let sddigit_min: String = SDDigit::MIN.to_string();
        let ddigit_max: String = DDigit::MAX.to_string();

        x.assign_str_base(&sddigit_min, DEC).unwrap();
        assert_eq!(&x, SDDigit::MIN);
        x.assign_str_base(&ddigit_max, DEC).unwrap();
        assert_eq!(&x, DDigit::MAX);
    }

    #[test]
    fn smoke() {
        let mut x = Arbi::zero();

        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_16 = get_uniform_die(i16::MIN, i16::MAX);

        for _ in 0..i16::MAX {
            let rv: SDDigit = die.sample(&mut rng);
            let s: String = rv.to_string();
            x.assign_str_base(&s, DEC).unwrap();
            assert_eq!(&x, rv);

            let rv_16: i16 = die_16.sample(&mut rng);
            let s: String = rv_16.to_string();
            x.assign_str_base(&s, DEC).unwrap();
            assert_eq!(&x, rv_16);
        }
    }
}
