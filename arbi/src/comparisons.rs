/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use crate::Digit;
use core::cmp::Ordering;

impl Ord for Arbi {
    fn cmp(&self, other: &Self) -> Ordering {
        Self::cmp_(self, other)
    }
}

impl PartialOrd for Arbi {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Arbi {
    fn eq(&self, other: &Self) -> bool {
        Self::cmp_(self, other) == Ordering::Equal
    }
}

impl Eq for Arbi {}

#[inline(always)]
pub(crate) fn s_size(digits: &[Digit]) -> usize {
    let mut len = digits.len();
    while len > 0 && digits[len - 1] == 0 {
        len -= 1;
    }
    len
}

pub(crate) fn s_cmp_impl(
    a: &[Digit],
    b: &[Digit],
    assume_normalized: bool,
) -> Ordering {
    let (a_size, b_size) = if assume_normalized {
        (a.len(), b.len())
    } else {
        (s_size(a), s_size(b))
    };
    match a_size.cmp(&b_size) {
        Ordering::Equal => {
            for i in (0..a_size).rev() {
                match a[i].cmp(&b[i]) {
                    Ordering::Equal => continue,
                    other => return other,
                }
            }
            Ordering::Equal
        }
        other => other,
    }
}

#[allow(dead_code)]
pub(crate) fn s_cmp(a: &[Digit], b: &[Digit]) -> Ordering {
    s_cmp_impl(a, b, false)
}

pub(crate) fn s_cmp_normalized(a: &[Digit], b: &[Digit]) -> Ordering {
    debug_assert!(
        a.is_empty() || a.last() != Some(&0),
        "slice a not normalized"
    );
    debug_assert!(
        b.is_empty() || b.last() != Some(&0),
        "slice b not normalized"
    );
    s_cmp_impl(a, b, true)
}

impl Arbi {
    // Assumes x, y >= 0
    pub(crate) fn cmp_abs(x: &Self, y: &Self) -> Ordering {
        #[allow(clippy::comparison_chain)]
        if x.size() > y.size() {
            Ordering::Greater
        } else if x.size() < y.size() {
            Ordering::Less
        } else {
            for i in (0..x.size()).rev() {
                if x.vec[i] > y.vec[i] {
                    return Ordering::Greater;
                } else if x.vec[i] < y.vec[i] {
                    return Ordering::Less;
                }
            }
            Ordering::Equal
        }
    }

    /// Return `Ordering::Less`, `Ordering::Equal`, or `Ordering::Greater`
    /// depending if x < y, x == y, or x > y.
    fn cmp_(x: &Self, y: &Self) -> Ordering {
        #[allow(clippy::comparison_chain)]
        if !x.is_negative() && y.is_negative() {
            // x >= 0, y < 0
            Ordering::Greater
        } else if x.is_negative() && !y.is_negative() {
            // x < 0, y >= 0
            Ordering::Less
        } else if x.is_negative() && y.is_negative() {
            // x, y < 0
            if x.size() > y.size() {
                Ordering::Less
            } else if x.size() < y.size() {
                Ordering::Greater
            } else {
                for i in (0..x.size()).rev() {
                    if x.vec[i] < y.vec[i] {
                        return Ordering::Greater;
                    } else if x.vec[i] > y.vec[i] {
                        return Ordering::Less;
                    }
                }
                Ordering::Equal
            }
        } else {
            // x, y >= 0
            Self::cmp_abs(x, y)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Arbi, DDigit, Digit, SDDigit};
    use core::cmp::Ordering;

    #[test]
    fn test_comparison_small_positive_numbers() {
        let a: Arbi = 123.into();
        let b: Arbi = 456.into();

        assert_eq!(a.cmp(&b), Ordering::Less);
        assert!(a < b);
        assert_eq!(b.cmp(&a), Ordering::Greater);
        assert!(b > a);

        let c: Arbi = 123.into();
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert!(a == c);
    }

    #[test]
    fn test_comparison_small_negative_numbers() {
        let a: Arbi = (-123).into();
        let b: Arbi = (-456).into();

        assert_eq!(a.cmp(&b), Ordering::Greater);
        assert!(a > b);
        assert_eq!(b.cmp(&a), Ordering::Less);
        assert!(b < a);

        let c: Arbi = (-123).into();
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert!(a == c);
    }

    #[test]
    fn test_comparison_small_positive_and_negative() {
        let a: Arbi = 123.into();
        let b: Arbi = (-456).into();

        assert_eq!(a.cmp(&b), Ordering::Greater);
        assert!(a > b);
        assert_eq!(b.cmp(&a), Ordering::Less);
        assert!(b < a);
    }

    #[test]
    fn test_comparison_magnitude_equal_numbers() {
        let a: Arbi = 123.into();
        let b: Arbi = (-123).into();

        assert_eq!(a.cmp(&b), Ordering::Greater);
        assert!(a > b);
        assert_eq!(b.cmp(&a), Ordering::Less);
        assert!(b < a);
    }

    #[test]
    fn test_zero_comparison() {
        let a: Arbi = 0.into();
        let b: Arbi = 0.into();

        assert_eq!(a.cmp(&b), Ordering::Equal);
        assert!(a == b);

        let c: Arbi = (-0).into();
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert!(a == c);
    }

    #[test]
    fn test_comparison_large_values() {
        let a: Arbi = ((Digit::MAX as DDigit) + 1).into();
        let b: Arbi = Digit::MAX.into();

        assert_eq!(a.cmp(&b), Ordering::Greater);
        assert!(a > b);

        assert_eq!(b.cmp(&a), Ordering::Less);
        assert!(b < a);

        let c: Arbi = ((Digit::MAX as SDDigit) + 1).into();
        assert_eq!(a.cmp(&c), Ordering::Equal);
        assert!(a == c);
    }

    #[test]
    fn test_gte() {
        let x = Arbi::from(10);
        let y = Arbi::from(10);
        let z = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(x >= y);
        assert!(x >= z);
        assert!(!(z >= x));
        assert!(!(zero >= x));
        assert!(x >= zero);
    }

    #[test]
    fn test_lte() {
        let x = Arbi::from(10);
        let y = Arbi::from(10);
        let z = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(x <= y);
        assert!(!(x <= z));
        assert!(z <= x);
        assert!(zero <= x);
        assert!(!(x <= zero));
    }

    #[test]
    fn test_gt() {
        let x = Arbi::from(10);
        let y = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(!(y > x));
        assert!(x > y);
        assert!(!(zero > x));
        assert!(x > zero);
        assert!(zero > y);
    }

    #[test]
    fn test_lt() {
        let x = Arbi::from(10);
        let y = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(y < x);
        assert!(!(x < y));
        assert!(zero < x);
        assert!(y < zero);
        assert!(!(x < zero));
    }

    #[test]
    fn test_ne() {
        let x = Arbi::from(10);
        let y = Arbi::from(10);
        let z = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(!(x != y));
        assert!(x != z);
        assert!(x != zero);
    }

    #[test]
    fn test_eq() {
        let x = Arbi::from(10);
        let y = Arbi::from(10);
        let z = Arbi::from(-10);
        let zero = Arbi::zero();

        assert!(x == y);
        assert!(!(x == z));
        assert!(!(x == zero));
    }

    enum BinOp {
        Eq,
        Ne,
        Gt,
        Lt,
        Gte,
        Lte,
    }

    fn test_binary_op_(op: BinOp) {
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };

        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) = (die.sample(&mut rng), die.sample(&mut rng));
            let (a, b) = (Arbi::from(a_in), Arbi::from(b_in));

            match op {
                BinOp::Eq => assert_eq!(a == b, a_in == b_in),
                BinOp::Ne => assert_eq!(a != b, a_in != b_in),
                BinOp::Gt => assert_eq!(a > b, a_in > b_in),
                BinOp::Lt => assert_eq!(a < b, a_in < b_in),
                BinOp::Gte => assert_eq!(a >= b, a_in >= b_in),
                BinOp::Lte => assert_eq!(a <= b, a_in <= b_in),
            }
        }
    }

    #[test]
    fn test_binary_op() {
        let ops = [
            BinOp::Eq,
            BinOp::Ne,
            BinOp::Gt,
            BinOp::Lt,
            BinOp::Gte,
            BinOp::Lte,
        ];

        for op in ops {
            test_binary_op_(op);
        }
    }
}
