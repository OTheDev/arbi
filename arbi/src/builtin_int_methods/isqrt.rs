/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT

We use Romano (2024) for integer square root. See
https://arxiv.org/abs/2406.07751. This implementation translates their provided
Java implementation closely, with some comments rewritten verbatim.
*/

use crate::util::float::MathOps;
use crate::Arbi;
use alloc::vec;

impl Arbi {
    /// Returns the square root of the number, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt(mut self) -> Self {
        self.isqrt_mut();
        self
    }

    /// Returns the square root of the number, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt_ref(&self) -> Self {
        self.clone().isqrt()
    }

    /// Replaces `self` with its square root, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt_mut(&mut self) {
        if self.is_negative() {
            panic!("argument of integer square root cannot be negative");
        }

        if self.is_zero() {
            return;
        }

        // Convert to BE to match Java algo
        self.vec.reverse();
        let mag_len = self.vec.len();

        // We'll store the sqrt result in a separate vec since it's smaller
        // Use self.vec directly for remainder calculations
        let mut sqrt = vec![0u32; (mag_len + 1) / 2];
        let mut r_begin = 0;
        let mut r_end;

        let mut digit: u64;
        let b = 0x100000000u64; // 2^32

        // First iteration
        if (mag_len & 1) == 0 {
            // Even length
            // Ensure round up of digit
            let val = ((self.vec[0] as u64) << 32) + (self.vec[1] as u64);
            digit = next_up_sqrt((val as f64).next_up_()) as u64;
            if digit == b {
                // Avoid overflow due to too high digit’s rounding
                digit -= 1;
            }

            let digit_sqr = digit * digit;
            let mut diff =
                (self.vec[1] as u64) as i64 - (digit_sqr & 0xFFFFFFFF) as i64;
            self.vec[1] = diff as u32;
            diff = (self.vec[0] as u64) as i64 - (digit_sqr >> 32) as i64
                + (diff >> 32);
            self.vec[0] = diff as u32;
            r_end = 2;

            // Check for the unlikely case of too high digit's rounding
            if (diff >> 32) != 0 {
                digit -= 1;
                // Add (digit + 1)^2 - digit^2 == 2*digit + 1
                let sum = (self.vec[1] as u64) + (digit << 1) + 1;
                self.vec[1] = sum as u32;
                self.vec[0] = ((self.vec[0] as u64) + (sum >> 32)) as u32;
            }
        } else {
            // Odd length
            // The integer sqrt is exact, no need to round up
            digit = ((self.vec[0] as u64) as f64).sqrt() as u64;
            let diff = (self.vec[0] as u64) - digit * digit;
            self.vec[0] = diff as u32;
            r_end = 1;
        }

        sqrt[0] = digit as u32; // Store digit
        let mut sqrt_f = Floating::new(digit);

        // Next iterations
        for sqrt_len in 1..sqrt.len() {
            // 1. Update remainder's begin
            while r_begin < r_end && self.vec[r_begin] == 0 {
                r_begin += 1;
            }

            // 2. Append the next block to the remainder
            // self.vec[r_end] = self.vec[r_end];
            // self.vec[r_end + 1] = self.vec[r_end + 1];
            r_end += 2;

            // 3. Guess the next digit
            // Compute remainder’s floating values
            let r_floor = Floating::value_of(&self.vec, r_begin, r_end);
            let r_ceil = r_floor.next_up();
            sqrt_f = sqrt_f.scale_by_power_of_2(32);

            // Ensure round up of digit
            digit = r_ceil
                .div(
                    &sqrt_f
                        .mul(&sqrt_f)
                        .next_down()
                        .add(&r_floor)
                        .next_down()
                        .sqrt()
                        .next_down()
                        .add(&sqrt_f)
                        .next_down(),
                )
                .next_up()
                .to_long();

            if digit != 0 {
                // 4. Compute the remainder
                if digit == b {
                    // Avoid overflow due to too high digit’s rounding
                    digit -= 1;
                }

                digit = Self::compute_remainder(
                    digit,
                    &mut sqrt,
                    sqrt_len,
                    &mut self.vec,
                    r_begin,
                    r_end,
                );

                // 5. Add the digit to sqrt's floating value, if its bits might
                // be representable
                if sqrt_len <= 2 {
                    if sqrt_len == 2 {
                        // Restore the correct rounding
                        sqrt_f = sqrt_f.next_up();
                    }
                    // Ensure round up of next digits
                    sqrt_f = sqrt_f.add(&Floating::new(digit)).next_down();
                }

                // 6. Store digit
                sqrt[sqrt_len] = digit as u32;
            }
        }

        // Replace self.vec with the sqrt result
        // Convert back to LE
        sqrt.reverse();
        self.vec = sqrt;

        self.trim();
    }

    fn compute_remainder(
        mut digit: u64,
        sqrt: &mut [u32],
        sqrt_len: usize,
        r: &mut [u32],
        r_begin: usize,
        r_end: usize,
    ) -> u64 {
        // Subtract common parts
        let mut r_pos = r_end - 1;
        let mut prod = digit * digit;
        let mut diff = (r[r_pos] as u64) as i64 - (prod & 0xFFFFFFFF) as i64;
        r[r_pos] = diff as u32;
        r_pos -= 1;

        let twice_digit = (digit << 1) & 0xFFFFFFFF;

        // rEnd >= 2*sqrtLen + 1, no risk that rPos becomes negative
        for i in (0..sqrt_len).rev() {
            prod = twice_digit * (sqrt[i] as u64) + (prod >> 32);
            diff = (r[r_pos] as u64) as i64 - (prod & 0xFFFFFFFF) as i64
                + (diff >> 32);
            r[r_pos] = diff as u32;
            r_pos -= 1;
        }

        // Borrow propagation
        if r_pos >= r_begin {
            prod >>= 32;
            diff = (r[r_pos] as u64) as i64 - prod as i64 + (diff >> 32);
            r[r_pos] = diff as u32;
            r_pos -= 1;

            if r_pos >= r_begin {
                diff = (r[r_pos] as u64) as i64 + (diff >> 32);
                r[r_pos] = diff as u32;
            }
            // The end: rEnd - rBegin <= sqrtLen + 3
        }

        // Check for the unlikely case of too high digit's rounding
        if (diff >> 32) != 0 {
            digit -= 1;

            // Add common parts
            r_pos = r_end - 1;
            let mut sum = (r[r_pos] as u64) + (digit << 1) + 1;
            r[r_pos] = sum as u32;
            r_pos -= 1;

            for i in (0..sqrt_len).rev() {
                sum = (r[r_pos] as u64) + ((sqrt[i] as u64) << 1) + (sum >> 32);
                r[r_pos] = sum as u32;
                r_pos -= 1;
            }

            // Carry propagation
            if r_pos >= r_begin {
                sum = (r[r_pos] as u64) + (sum >> 32);
                r[r_pos] = sum as u32;
                r_pos -= 1;

                if r_pos >= r_begin {
                    // Remainder’s length can’t be larger than sqrtLen + 2
                    r[r_pos] = 0;
                }
                // The end: rEnd - rBegin <= sqrtLen + 3
            }
        }

        digit
    }
}

fn next_up_sqrt(val: f64) -> f64 {
    let sqrt_val = val.sqrt();
    sqrt_val.next_up_()
}

#[derive(Clone, Debug)]
struct Floating {
    /// this == signif * 2^exp. if this != 0, then 1 <= signif < 2
    signif: f64,
    exp: i64,
}

impl Floating {
    const ZERO: Self = Self {
        signif: 0.0,
        exp: i64::MIN,
    };
    const MIN_VALUE: Self = Self {
        signif: 1.0,
        exp: i64::MIN,
    };

    fn new(n: u64) -> Self {
        if n == 0 {
            Self::ZERO
        } else {
            let exp = 63 - n.leading_zeros() as i64;
            // Java: n >= 0 ? n : n + 0x1p64
            let val = if n < 0x8000000000000000 {
                n as f64
            } else {
                n as f64 + 18446744073709551616.0 // 0x1p64
            };

            let signif = if exp == 0 {
                val
            } else {
                // Java: Double.parseDouble("0x1p-" + exp)
                val * 2.0f64.powi(-(exp as i32))
            };

            Self { signif, exp }
        }
    }

    /// For reasons of speed, if the argument cannot be represented exactly, the
    /// magnitude is simply truncated: least significant bits are just
    /// discarded.
    fn value_of(mag: &[u32], begin: usize, end: usize) -> Self {
        let len = end - begin;
        if len == 0 {
            return Self::ZERO;
        }

        if len <= 2 {
            let mut val = mag[begin] as u64;
            if len == 2 {
                val = (val << 32) | (mag[begin + 1] as u64);
            }
            return Self::new(val);
        }

        let bit_len = (len << 5) - mag[begin].leading_zeros() as usize;

        // We need the top PRECISION bits, including the "implicit" one bit.
        // signif will contain the top PRECISION bits.
        let precision = 53; // Double.PRECISION in Java
        let shift = (bit_len as i32) - precision;
        let shift2 = -shift;

        let (mut high_bits, mut low_bits) = if (shift & 0x1f) == 0 {
            (mag[begin], mag[begin + 1])
        } else {
            let high = mag[begin].wrapping_shr(shift as u32);
            let low = (mag[begin].wrapping_shl(shift2 as u32))
                | (mag[begin + 1].wrapping_shr(shift as u32));
            (high, low)
        };

        if high_bits == 0 {
            high_bits = low_bits;
            low_bits = (mag[begin + 1].wrapping_shl(shift2 as u32))
                | (if begin + 2 < mag.len() {
                    mag[begin + 2].wrapping_shr(shift as u32)
                } else {
                    0
                });
        }

        let mut signif = ((high_bits as u64) << 32) | (low_bits as u64);
        signif ^= 1u64 << (precision - 1); // Remove the implied bit

        // Java: ((long) Double.MAX_EXPONENT << (Double.PRECISION - 1)) | signif
        let bits = (((f64::MAX_EXP - 1) as u64)  // add bias
            << (precision - 1))
            | signif;
        let signif_f = f64::from_bits(bits);

        Self {
            signif: signif_f,
            exp: (bit_len - 1) as i64,
        }
    }

    fn to_long(&self) -> u64 {
        if self.signif == 0.0 {
            return 0;
        }

        let two_to_52 = 1u64 << 52; // Double.PRECISION - 1
        let bits = self.signif.to_bits();
        let bits = (bits & (two_to_52 - 1)) | two_to_52;
        let shift = self.exp.wrapping_sub(52); // Double.PRECISION - 1

        if shift >= 0 {
            bits.wrapping_shl(shift as u32)
        } else {
            bits.wrapping_shr(-shift as u32)
        }
    }

    fn next_up(&self) -> Self {
        if self.signif == 0.0 {
            return Self::MIN_VALUE;
        }

        let res_signif = self.signif.next_up_();
        if res_signif >= 2.0 {
            Self {
                signif: res_signif / 2.0,
                exp: self.exp + 1,
            }
        } else {
            Self {
                signif: res_signif,
                exp: self.exp,
            }
        }
    }

    fn next_down(&self) -> Self {
        if self.signif == 0.0 || self.equals(&Self::MIN_VALUE) {
            return Self::ZERO;
        }

        let res_signif = self.signif.next_down_();
        if res_signif < 1.0 {
            Self {
                signif: res_signif * 2.0,
                exp: self.exp - 1,
            }
        } else {
            Self {
                signif: res_signif,
                exp: self.exp,
            }
        }
    }

    /// this * 2^n
    fn scale_by_power_of_2(&self, n: i64) -> Self {
        if self.signif == 0.0 {
            return Self::ZERO;
        }
        Self {
            signif: self.signif,
            exp: self.exp + n,
        }
    }

    fn add(&self, x: &Self) -> Self {
        if self.signif == 0.0 {
            return x.clone();
        }
        if x.signif == 0.0 {
            return self.clone();
        }

        let (big, little) = if self.exp > x.exp {
            (self, x)
        } else {
            (x, self)
        };

        // result == 2^big.exp * (big.signif + little.signif * 2^(little.exp - big.exp))
        let mut res_exp = big.exp;
        let mut res_signif = big.signif;
        let scale = little.exp - big.exp;

        // if (little.signif * 2^(little.exp - big.exp) < 2^-53) then little is
        // too small and does not affect the result
        if scale >= -53 {
            // -Double.PRECISION
            if scale == 0 {
                res_signif += little.signif;
            } else {
                // Java: Double.parseDouble("0x1p" + scale)
                res_signif += little.signif * 2.0f64.powi(scale as i32);
            }

            // Carry propagation
            if res_signif >= 2.0 {
                res_signif /= 2.0;
                res_exp += 1;
            }
        }

        Self {
            signif: res_signif,
            exp: res_exp,
        }
    }

    fn mul(&self, x: &Self) -> Self {
        if self.signif == 0.0 || x.signif == 0.0 {
            return Self::ZERO;
        }

        let mut res_exp = self.exp + x.exp;
        let mut res_signif = self.signif * x.signif;

        // Carry propagation
        if res_signif >= 2.0 {
            res_signif /= 2.0;
            res_exp += 1;
        }

        Self {
            signif: res_signif,
            exp: res_exp,
        }
    }

    fn div(&self, x: &Self) -> Self {
        if self.signif == 0.0 {
            return Self::ZERO;
        }

        let res_exp = self.exp.wrapping_sub(x.exp);

        // Exponent underflow iff the exponents have different signs and the
        // sign of resExp is different from the sign of this.exp
        if ((self.exp ^ x.exp) & (self.exp ^ res_exp)) < 0 {
            return Self::ZERO;
        }

        let mut res_signif = self.signif / x.signif;
        let mut res_exp = res_exp;

        // Borrow propagation
        if res_signif < 1.0 {
            if res_exp == i64::MIN {
                // Exponent underflow
                return Self::ZERO;
            }
            res_signif *= 2.0;
            res_exp -= 1;
        }

        Self {
            signif: res_signif,
            exp: res_exp,
        }
    }

    fn sqrt(&self) -> Self {
        if self.signif == 0.0 {
            return Self::ZERO;
        }

        if (self.exp & 1) == 1 {
            Self {
                signif: (2.0 * self.signif).sqrt(),
                exp: (self.exp - 1) >> 1,
            }
        } else {
            Self {
                signif: self.signif.sqrt(),
                exp: self.exp >> 1,
            }
        }
    }

    fn equals(&self, other: &Self) -> bool {
        self.signif == other.signif && self.exp == other.exp
    }
}

#[cfg(test)]
mod tests {
    use crate::uints::UnsignedUtilities;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit, QDigit};

    #[test]
    fn test_isqrt_basic() {
        for i in 0..11000u32 {
            assert_eq!(Arbi::from(i).isqrt(), i.isqrt_());
        }
    }

    #[test]
    #[should_panic = "argument of integer square root cannot be negative"]
    fn test_isqrt_negative() {
        let val = Arbi::from(-1);
        val.isqrt();
    }

    #[test]
    fn test_digit_boundaries() {
        let dmax = Digit::MAX;
        let dmaxp1 = dmax as DDigit + 1;
        let ddmax = DDigit::MAX;
        let ddmaxp1 = ddmax as QDigit + 1;

        assert_eq!(Arbi::from(dmax).isqrt(), dmax.isqrt_());
        assert_eq!(Arbi::from(dmaxp1).isqrt(), dmaxp1.isqrt_());
        assert_eq!(Arbi::from(ddmax).isqrt(), ddmax.isqrt_());
        assert_eq!(Arbi::from(ddmaxp1).isqrt(), ddmaxp1.isqrt_());
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_digit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());
        }
    }
}
