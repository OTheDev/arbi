/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::from_string::ParseError;
use crate::Arbi;
use crate::Base;

impl Arbi {
    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
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
    ///         ParseError::InvalidDigit => panic!("Found an invalid digit"),
    ///         ParseError::Empty => panic!("Found an empty string"),
    ///     },
    /// }
    ///
    /// if let Err(e) = x.assign_str_radix("7c2ecdfacad74e0f0101b", 16) {
    ///     panic!("Parsing error: {}", e);
    /// }
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// The `Arbi` integer will remain in its original state if a parsing error
    /// occurs:
    /// ```
    /// use arbi::{Arbi, Assign, ParseError};
    ///
    /// let mut x = Arbi::from(u128::MAX);
    /// assert_eq!(x, u128::MAX);
    ///
    /// match x.assign_str_radix("7c2ecdfacad74e0f0101b", 15) {
    ///     Ok(_) => panic!(),
    ///     Err(e) => {
    ///         assert!(matches!(e, ParseError::InvalidDigit));
    ///         assert_eq!(x, u128::MAX);
    ///     }
    /// }
    /// ```
    ///
    /// Panics on invalid `radix` values
    /// ```should_panic
    /// use arbi::Arbi;
    ///
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
    /// assert!(matches!(
    ///     a.assign_str_radix("   - ", 10),
    ///     Err(ParseError::Empty)
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

        self.from_str_base_inplace(s, base)
    }

    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
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
    ///         ParseError::InvalidDigit => panic!("Found an invalid digit"),
    ///         ParseError::Empty => panic!("Found an empty string"),
    ///     },
    /// }
    ///
    /// if let Err(e) = x.assign_str_base("7c2ecdfacad74e0f0101b", HEX) {
    ///     panic!("Parsing error: {}", e);
    /// }
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// The `Arbi` integer will remain in its original state if a parsing error
    /// occurs:
    /// ```
    /// use arbi::{Arbi, Base, ParseError};
    ///
    /// let mut x = Arbi::from(u128::MAX);
    /// assert_eq!(x, u128::MAX);
    ///
    /// match x
    ///     .assign_str_base("7c2ecdfacad74e0f0101b", Base::try_from(15).unwrap())
    /// {
    ///     Ok(_) => panic!(),
    ///     Err(e) => {
    ///         assert!(matches!(e, ParseError::InvalidDigit));
    ///         assert_eq!(x, u128::MAX);
    ///     }
    /// }
    /// ```
    ///
    /// Example invalid strings:
    /// ```
    /// use arbi::{base::DEC, Arbi, ParseError};
    ///
    /// let mut a = Arbi::zero();
    ///
    /// assert!(matches!(
    ///     a.assign_str_base("   - ", DEC),
    ///     Err(ParseError::Empty)
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
        self.from_str_base_inplace(s, base)
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
