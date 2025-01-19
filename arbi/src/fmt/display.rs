/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{base::DEC, Arbi};
use core::fmt;

/// Outputs the base-10 (decimal) representation of an `Arbi` integer.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// assert_eq!(format!("{}", Arbi::from(12345)), "12345");
/// assert_eq!(format!("{}", Arbi::from(-12345)), "-12345");
/// ```
impl fmt::Display for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_base(DEC))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{SDDigit, SDigit, SQDigit};
    use alloc::format;
    use alloc::string::ToString;

    #[test]
    fn test_display_zero() {
        let arbi = Arbi::zero();
        assert_eq!(format!("{}", arbi), "0");
    }

    #[test]
    fn test_display_positive() {
        let arbi = Arbi::from(1234);
        assert_eq!(format!("{}", arbi), "1234");
    }

    #[test]
    fn test_display_negative() {
        let arbi = Arbi::from(-1234);
        assert_eq!(format!("{}", arbi), "-1234");
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let die_s = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_m = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_l = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for i in i16::MIN..i16::MAX {
            let rs = die_s.sample(&mut rng);
            let rm = die_m.sample(&mut rng);
            let rl = die_l.sample(&mut rng);

            assert_eq!(format!("{}", Arbi::from(rs)), rs.to_string());
            assert_eq!(format!("{}", Arbi::from(rm)), rm.to_string());
            assert_eq!(format!("{}", Arbi::from(rl)), rl.to_string());

            assert_eq!(format!("{}", Arbi::from(i)), i.to_string());
        }
    }
}
