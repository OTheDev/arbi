/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use core::f64;

/// Replacement for f64::floor() in no-std.
///
/// The motivation behind implementing this is that it was the only function
/// when converting from std to no-std that was not available in core. Floor
/// might not be needed at all in the future.
pub(crate) fn floor(x: f64) -> f64 {
    const MANTISSA_MASK: u64 = 0x000fffffffffffff_u64;
    const ABSOLUTE_MASK: u64 = 0x7fffffffffffffff_u64;
    const IMPLICIT_ONE: i64 = 0x0010000000000000_i64;

    let mut x_i64: i64 = x.to_bits() as i64;
    let unbiased_exponent: i32 = (0x7ff & (x_i64 >> 52)) as i32 - 0x3ff;

    match unbiased_exponent {
        0x400 => {
            assert!(x.is_infinite() || x.is_nan());
            x + x
        } // f

        exp if exp < 0 => {
            if x_i64 >= 0 {
                x_i64 = 0; // a
            } else if (ABSOLUTE_MASK as i64 & x_i64) != 0 {
                x_i64 = 0xbff0000000000000_u64 as i64; // b
            }

            f64::from_bits(x_i64 as u64)
        }

        exp if (0..52).contains(&exp) => {
            let m = MANTISSA_MASK >> exp;
            if (m as i64 & x_i64) == 0 {
                x // c
            } else {
                if x_i64 < 0 {
                    x_i64 += IMPLICIT_ONE >> exp as i64; // d
                }
                x_i64 &= !(m as i64);

                f64::from_bits(x_i64 as u64) // e
            }
        }

        _ => x, // g
    }
}

#[cfg(test)]
mod tests {
    #[cfg(test)]
    extern crate std;

    use super::*;
    use crate::util::test::{get_seedable_rng, Rng};
    use std::f64;

    #[test]
    fn test_floor_marked_code_paths() {
        // a
        assert_eq!(floor(0.0_f64), (0.0_f64).floor());

        // b
        assert_eq!(
            floor(-0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015134722735375557_f64),
            (-0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015134722735375557_f64).floor()
        );

        // c
        assert_eq!(floor(33.0_f64), (33.0_f64).floor());

        // d
        assert_eq!(floor(-2.5_f64), (-2.5_f64).floor());

        // e
        assert_eq!(floor(21.192_f64), (21.192_f64).floor());

        // f
        assert_eq!(floor(f64::INFINITY), (f64::INFINITY).floor());
        assert_eq!(floor(f64::NEG_INFINITY), (f64::NEG_INFINITY).floor());
        assert!(floor(f64::NAN).is_nan() && (f64::NAN).floor().is_nan());

        // g
        assert_eq!(
            floor(9007199254740992.0_f64),
            (9007199254740992.0_f64).floor()
        );
    }

    #[test]
    fn test_floor_against_std() {
        let test_values = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            2.5,
            -2.5,
            3.9999999999,
            -3.9999999999,
            987654321.987654321,
            -987654321.987654321,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MIN_POSITIVE,
            f64::MIN_POSITIVE / (1u64 << 52) as f64,
            (1_i64 << 53) as f64,
            -(1_i64 << 53) as f64,
            f64::MAX,
            -f64::MAX,
            f64::MIN,
            -f64::MIN,
        ];

        for &value in &test_values {
            let expected = value.floor();
            let result = floor(value);
            if expected.is_nan() {
                assert!(result.is_nan(), "Failed on value: {}", value);
                continue;
            }
            assert_eq!(
                expected.to_bits(),
                result.to_bits(),
                "Failed on value: {}",
                value
            );
        }

        let (mut rng, _) = get_seedable_rng();

        for _ in 0..i16::MAX {
            let r_u64: u64 = rng.gen();
            let r = f64::from_bits(r_u64);

            let expected = r.floor();
            let result = floor(r);
            if expected.is_nan() {
                assert!(result.is_nan(), "Failed on value: {}", r);
                continue;
            }
            assert_eq!(
                expected.to_bits(),
                result.to_bits(),
                "Failed on value: {}",
                r
            );
        }
    }
}
