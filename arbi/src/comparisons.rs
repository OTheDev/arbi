/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
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
            return Ordering::Equal;
        }
    }

    /// Return `Ordering::Less`, `Ordering::Equal`, or `Ordering::Greater`
    /// depending if x < y, x == y, or x > y.
    fn cmp_(x: &Self, y: &Self) -> Ordering {
        #[allow(clippy::comparison_chain)]
        if !x.negative() && y.negative() {
            // x >= 0, y < 0
            Ordering::Greater
        } else if x.negative() && !y.negative() {
            // x < 0, y >= 0
            Ordering::Less
        } else if x.negative() && y.negative() {
            // x, y < 0
            if x.size() > y.size() {
                return Ordering::Less;
            } else if x.size() < y.size() {
                return Ordering::Greater;
            } else {
                for i in (0..x.size()).rev() {
                    if x.vec[i] < y.vec[i] {
                        return Ordering::Greater;
                    } else if x.vec[i] > y.vec[i] {
                        return Ordering::Less;
                    }
                }
                return Ordering::Equal;
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
