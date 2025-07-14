/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

// Equivalent to 2.0f64.powi(n) or Java's Double.parseDouble("0x1p" + n) for
// any n (i32).
pub(crate) fn fpow2(n: i32) -> f64 {
    if (-1022..=1023).contains(&n) {
        // Normal
        f64::from_bits(((1023 + n as i64) << 52) as u64)
    } else if (-1074..-1022).contains(&n) {
        // Subnormal
        f64::from_bits(1u64 << (n + 1074))
    } else if n < -1074 {
        // Underflow to zero
        0.0
    } else {
        // n > 1023: overflow
        f64::INFINITY
    }
}

pub(crate) trait MathOps {
    // NOTE: next_up(), next_down() are not available in core and std until 1.86
    fn next_up_(self) -> Self;
    fn next_down_(self) -> Self;
    // fn sqrt(self) -> Self;
    // fn powf(self, n: Self) -> Self;
}

impl MathOps for f64 {
    fn next_up_(self) -> Self {
        // if self.is_nan(), this returns self;
        if self.is_nan() {
            return self;
        }
        // if self is NEG_INFINITY, this returns MIN;
        if self == f64::NEG_INFINITY {
            return f64::MIN;
        }
        // if self is -TINY, this returns -0.0;
        if self == -f64::from_bits(1) {
            return -0.0;
        }
        // if self is -0.0 or +0.0, this returns TINY;
        if self == 0.0 {
            return f64::from_bits(1);
        }
        // if self is MAX or INFINITY, this returns INFINITY;
        if self == f64::MAX || self == f64::INFINITY {
            return f64::INFINITY;
        }
        // otherwise the unique least value greater than self is returned.
        let bits = self.to_bits();
        if self > 0.0 {
            f64::from_bits(bits + 1)
        } else {
            f64::from_bits(bits - 1)
        }
    }

    fn next_down_(self) -> Self {
        // if self.is_nan(), this returns self;
        if self.is_nan() {
            return self;
        }
        // if self is INFINITY, this returns MAX;
        if self == f64::INFINITY {
            return f64::MAX;
        }
        // if self is TINY, this returns 0.0;
        if self == f64::from_bits(1) {
            return 0.0;
        }
        // if self is -0.0 or +0.0, this returns -TINY;
        if self == 0.0 {
            return -f64::from_bits(1);
        }
        // if self is MIN or NEG_INFINITY, this returns NEG_INFINITY;
        if self == f64::MIN || self == f64::NEG_INFINITY {
            return f64::NEG_INFINITY;
        }
        // otherwise the unique greatest value less than self is returned.
        let bits = self.to_bits();
        if self > 0.0 {
            f64::from_bits(bits - 1)
        } else {
            f64::from_bits(bits + 1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::MathOps;

    #[test]
    fn test_next_up() {
        assert!(f64::NAN.next_up_().is_nan());
        assert_eq!(f64::NEG_INFINITY.next_up_(), f64::MIN);
        assert_eq!(f64::INFINITY.next_up_(), f64::INFINITY);
        assert_eq!(0.0f64.next_up_(), f64::from_bits(1));
        assert_eq!((-0.0f64).next_up_(), f64::from_bits(1));
        assert_eq!((-f64::from_bits(1)).next_up_(), -0.0);
        assert_eq!(1.0f64.next_up_(), 1.0 + f64::EPSILON);
        assert_eq!(f64::MAX.next_up_(), f64::INFINITY);
    }

    #[test]
    fn test_next_down() {
        assert!(f64::NAN.next_down_().is_nan());
        assert_eq!(f64::INFINITY.next_down_(), f64::MAX);
        assert_eq!(f64::NEG_INFINITY.next_down_(), f64::NEG_INFINITY);
        assert_eq!(0.0f64.next_down_(), -f64::from_bits(1));
        assert_eq!((-0.0f64).next_down_(), -f64::from_bits(1));
        assert_eq!(f64::from_bits(1).next_down_(), 0.0);
        assert_eq!(f64::MIN.next_down_(), f64::NEG_INFINITY);
    }

    // The identity x.next_up() == -(-x).next_down() holds for all non-NaN x.
    // When x is finite x == x.next_up().next_down() also holds.
    // The identity x.next_down() == -(-x).next_up() holds for all non-NaN x.
    // When x is finite x == x.next_down().next_up() also holds.
    #[test]
    fn test_identity() {
        let test_values = [
            0.1,
            -0.1,
            1.0,
            -1.0,
            100.0,
            -100.0,
            f64::MIN,
            f64::MAX,
            f64::NEG_INFINITY,
            f64::INFINITY,
        ];

        for &x in &test_values {
            assert_eq!(x.next_up_(), -(-x).next_down_());
            if x.is_finite() {
                assert_eq!(x, x.next_up_().next_down_());
            }
            assert_eq!(x.next_down_(), -(-x).next_up_());
            if x.is_finite() {
                assert_eq!(x, x.next_down_().next_up_());
            }
        }
    }
}
