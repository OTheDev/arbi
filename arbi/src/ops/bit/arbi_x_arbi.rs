/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not,
};

/// See [BitAnd](#impl-BitAnd<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitAnd<Arbi> for Arbi {
    type Output = Arbi;
    fn bitand(mut self, mut rhs: Self) -> Self::Output {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_and(&rhs);
        self
    }
}

/// See [BitAnd](#impl-BitAnd<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitAnd<&'a Arbi> for Arbi {
    type Output = Arbi;
    fn bitand(mut self, rhs: &'a Self) -> Self::Output {
        self.inplace_bitwise_and(rhs);
        self
    }
}

/// Mathematically, given two integers \\( x, y \\) with coefficients
/// \\( x\_{i}, y\_{i} \\) of their binary representation, the result of
/// \\( x \\; \\& \\; y \\) (bitwise AND) is an integer \\( r \\) with base-2
/// coefficients \\( r\_{i} \\) such that
/// \\[
///     r\_{i} = 1 \Longleftrightarrow x\_{i} = 1 \wedge y\_{i} = 1
/// \\]
impl<'a> BitAnd<&'a Arbi> for &Arbi {
    type Output = Arbi;
    fn bitand(self, rhs: &'a Arbi) -> Self::Output {
        let mut ret = Arbi::zero();
        ret.assign_bitwise_and(self, rhs);
        ret
    }
}

/// See [BitAnd](#impl-BitAnd<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitAndAssign<Arbi> for Arbi {
    fn bitand_assign(&mut self, mut rhs: Self) {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_and(&rhs);
    }
}

/// See [BitAnd](#impl-BitAnd<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitAndAssign<&'a Arbi> for Arbi {
    fn bitand_assign(&mut self, rhs: &'a Self) {
        self.inplace_bitwise_and(rhs);
    }
}

/// See [BitOr](#impl-BitOr<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitOr<Arbi> for Arbi {
    type Output = Arbi;
    fn bitor(mut self, mut rhs: Self) -> Self::Output {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_ior(&rhs);
        self
    }
}

/// See [BitOr](#impl-BitOr<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitOr<&'a Arbi> for Arbi {
    type Output = Arbi;
    fn bitor(mut self, rhs: &'a Self) -> Self::Output {
        self.inplace_bitwise_ior(rhs);
        self
    }
}

/// Mathematically, given two integers \\( x, y \\) with coefficients
/// \\( x\_{i}, y\_{i} \\) of their binary representation, the result of
/// \\( x \\; | \\; y \\) (bitwise inclusive OR) is an integer \\( r \\) with
/// base-2 coefficients \\( r\_{i} \\) such that
/// \\[
///     r\_{i} = 1 \Longleftrightarrow x\_{i} = 1 \lor y\_{i} = 1
/// \\]
impl<'a> BitOr<&'a Arbi> for &Arbi {
    type Output = Arbi;
    fn bitor(self, rhs: &'a Arbi) -> Self::Output {
        let mut ret = Arbi::zero();
        ret.assign_bitwise_ior(self, rhs);
        ret
    }
}

/// See [BitOr](#impl-BitOr<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitOrAssign<Arbi> for Arbi {
    fn bitor_assign(&mut self, mut rhs: Self) {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_ior(&rhs);
    }
}

/// See [BitOr](#impl-BitOr<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitOrAssign<&'a Arbi> for Arbi {
    fn bitor_assign(&mut self, rhs: &'a Self) {
        self.inplace_bitwise_ior(rhs);
    }
}

/// See [BitXor](#impl-BitXor<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitXor<Arbi> for Arbi {
    type Output = Arbi;
    fn bitxor(mut self, mut rhs: Self) -> Self::Output {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_xor(&rhs);
        self
    }
}

/// See [BitXor](#impl-BitXor<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitXor<&'a Arbi> for Arbi {
    type Output = Arbi;
    fn bitxor(mut self, rhs: &'a Self) -> Self::Output {
        self.inplace_bitwise_xor(rhs);
        self
    }
}

/// Mathematically, given two integers \\( x, y \\) with coefficients
/// \\( x\_{i}, y\_{i} \\) of their binary representation, the result of
/// \\( x \\; ^\wedge \\; y \\) (bitwise exclusive OR) is an integer \\( r \\)
/// with base-2 coefficients \\( r\_{i} \\) such that
/// \\[
///     r\_{i} = 1 \Longleftrightarrow (x\_{i} = 1 \wedge y\_{i} = 0) \lor
///                                    (x\_{i} = 0 \wedge y\_{i} = 1)
/// \\]
impl<'a> BitXor<&'a Arbi> for &Arbi {
    type Output = Arbi;
    fn bitxor(self, rhs: &'a Arbi) -> Self::Output {
        let mut ret = Arbi::zero();
        ret.assign_bitwise_xor(self, rhs);
        ret
    }
}

/// See [BitXor](#impl-BitXor<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl BitXorAssign<Arbi> for Arbi {
    fn bitxor_assign(&mut self, mut rhs: Self) {
        self.swap_if_smaller_capacity(&mut rhs);
        self.inplace_bitwise_xor(&rhs);
    }
}

/// See [BitXor](#impl-BitXor<%26Arbi>-for-%26Arbi) for the mathematical
/// semantics.
impl<'a> BitXorAssign<&'a Arbi> for Arbi {
    fn bitxor_assign(&mut self, rhs: &'a Self) {
        self.inplace_bitwise_xor(rhs);
    }
}

/// Unary complement operator. Return the ones' complement of this integer.
///
/// This is done in-place, using the moved-in value.
///
/// # Example
/// ```
/// use arbi::{Arbi, Assign};
///
/// let mut a = Arbi::zero();
/// a = !a; // in-place
/// assert_eq!(a, -1);
/// assert_eq!(a, !0);
///
/// a.assign(u16::MAX);
/// a = !a; // in-place
/// assert_eq!(a, -65536);
/// assert_eq!(a, !(u16::MAX as i32));
/// ```
///
/// ## Complexity
/// \\( O(n) \\)
impl Not for Arbi {
    type Output = Arbi;
    fn not(mut self) -> Self::Output {
        self += 1;
        self.negate_mut();
        self
    }
}

/// Unary complement operator. Return a new integer representing the ones'
/// complement of this integer.
///
/// This involves cloning the referenced `Arbi` integer.
///
/// # Example
/// ```
/// use arbi::{Arbi, Assign};
///
/// let mut a = Arbi::zero();
/// a = !&a;
/// assert_eq!(a, -1);
/// assert_eq!(a, !0);
///
/// a.assign(u16::MAX);
/// a = !&a;
/// assert_eq!(a, -65536);
/// assert_eq!(a, !(u16::MAX as i32));
/// ```
///
/// ## Complexity
/// \\( O(n) \\)
impl Not for &Arbi {
    type Output = Arbi;
    fn not(self) -> Self::Output {
        !(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Digit, SDDigit};
    use alloc::vec;
    use alloc::vec::Vec;

    #[derive(Debug, Copy, Clone)]
    #[allow(dead_code)]
    enum Op {
        And,
        Or,
        Xor,
        AndAssign,
        OrAssign,
        XorAssign,
    }

    fn check_op(op: Op, mut lhs: SDDigit, rhs: SDDigit) {
        let mut lhs_arbi = Arbi::from(lhs);
        let val = match op {
            Op::And => {
                assert!(Arbi::from(lhs) & Arbi::from(rhs) == lhs & rhs);
                (&lhs_arbi & &Arbi::from(rhs)) == (lhs & rhs)
            }
            Op::Or => {
                assert!(Arbi::from(lhs) | Arbi::from(rhs) == lhs | rhs);
                (&lhs_arbi | &Arbi::from(rhs)) == (lhs | rhs)
            }
            Op::Xor => {
                assert!(Arbi::from(lhs) ^ Arbi::from(rhs) == lhs ^ rhs);
                (&lhs_arbi ^ &Arbi::from(rhs)) == (lhs ^ rhs)
            }
            Op::AndAssign => {
                lhs_arbi &= Arbi::from(rhs);
                lhs &= rhs;

                lhs_arbi == lhs
            }
            Op::OrAssign => {
                lhs_arbi |= Arbi::from(rhs);
                lhs |= rhs;

                lhs_arbi == lhs
            }
            Op::XorAssign => {
                lhs_arbi ^= Arbi::from(rhs);
                lhs ^= rhs;

                lhs_arbi == lhs
            }
        };

        assert!(val, "Failure with lhs: {}, rhs: {}, op: {:?}", lhs, rhs, op);
    }

    fn test_bitwise_operation(op: Op) {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_small = get_uniform_die(-25, 25);
        let die_digit = get_uniform_die(
            Digit::MAX as SDDigit - 25,
            Digit::MAX as SDDigit + 25,
        );

        for _ in 0..i16::MAX {
            let (ra, rb) = (die.sample(&mut rng), die.sample(&mut rng));
            let (ra_small, rb_small) =
                (die_small.sample(&mut rng), die_small.sample(&mut rng));
            let (ra_digit, rb_digit) =
                (die_digit.sample(&mut rng), die_digit.sample(&mut rng));

            check_op(op, ra, rb);
            check_op(op, ra_small, rb_small);
            check_op(op, ra_digit, rb_digit);
            check_op(op, ra, ra_small);
            check_op(op, ra, ra_digit);
            check_op(op, ra_small, ra_digit);
        }
    }

    fn get_data() -> (Arbi, Arbi, Arbi) {
        (Arbi::zero(), Arbi::from(12345), Arbi::from(-6789))
    }

    #[test]
    fn bitwise_and() {
        let (zero, pos, neg) = get_data();

        assert_eq!(&pos & &pos, 12345);
        assert_eq!(&neg & &neg, -6789);
        assert_eq!(&zero & &pos, 0);
        assert_eq!(&zero & &neg, 0);
        assert_eq!(&pos & &neg, 8249);

        test_bitwise_operation(Op::And);
    }

    #[test]
    fn bitwise_or() {
        let (zero, pos, neg) = get_data();

        assert_eq!(&pos | &pos, 12345);
        assert_eq!(&neg | &neg, -6789);
        assert_eq!(&zero | &pos, 12345);
        assert_eq!(&zero | &neg, -6789);
        assert_eq!(&pos | &neg, -2693);

        test_bitwise_operation(Op::Or);
    }

    #[test]
    fn bitwise_xor() {
        let (zero, pos, neg) = get_data();

        assert_eq!(&pos ^ &pos, 0);
        assert_eq!(&neg ^ &neg, 0);
        assert_eq!(&zero ^ &pos, 12345);
        assert_eq!(&zero ^ &neg, -6789);
        assert_eq!(&pos ^ &neg, -10942);

        test_bitwise_operation(Op::Xor);
    }

    #[test]
    fn bitwise_and_assignment() {
        let (zero, pos, neg) = get_data();

        let mut res = pos.clone();
        res &= &pos;
        assert_eq!(res, 12345);

        let mut res = neg.clone();
        res &= &neg;
        assert_eq!(res, -6789);

        let mut res = pos.clone();
        res &= &neg;
        assert_eq!(res, 8249);

        let mut res = zero.clone();
        res &= &pos;
        assert_eq!(res, 0);

        let mut res = zero.clone();
        res &= &neg;
        assert_eq!(res, 0);

        test_bitwise_operation(Op::AndAssign);
    }

    #[test]
    fn bitwise_or_assignment() {
        let (zero, pos, neg) = get_data();

        let mut res = pos.clone();
        res |= &pos;
        assert_eq!(res, 12345);

        let mut res = neg.clone();
        res |= &neg;
        assert_eq!(res, -6789);

        let mut res = zero.clone();
        res |= &pos;
        assert_eq!(res, 12345);

        let mut res = zero.clone();
        res |= &neg;
        assert_eq!(res, -6789);

        let mut res = pos.clone();
        res |= &neg;
        assert_eq!(res, -2693);

        test_bitwise_operation(Op::OrAssign);
    }

    #[test]
    fn bitwise_xor_assignment() {
        let (zero, pos, neg) = get_data();

        let mut res = pos.clone();
        res ^= &pos;
        assert_eq!(res, 0);

        let mut res = neg.clone();
        res ^= &neg;
        assert_eq!(res, 0);

        let mut res = zero.clone();
        res ^= &pos;
        assert_eq!(res, 12345);

        let mut res = zero.clone();
        res ^= &neg;
        assert_eq!(res, -6789);

        let mut res = pos.clone();
        res ^= &neg;
        assert_eq!(res, -10942);

        test_bitwise_operation(Op::XorAssign);
    }

    #[test]
    fn bitwise_not_digit_boundaries() {
        assert_eq!(!Arbi::zero(), -1);
        assert_eq!(!Arbi::one(), -2);
        assert_eq!(!Arbi::from(Digit::MAX), !(Digit::MAX as SDDigit));
        assert_eq!(!Arbi::from(Digit::MAX), -(Digit::MAX as SDDigit) - 1);
    }

    #[test]
    fn bitwise_not_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_mdigit = get_uniform_die(
            Digit::MAX as SDDigit / 4,
            Digit::MAX as SDDigit / 2,
        );
        let die_msddigit = get_uniform_die(SDDigit::MAX / 4, SDDigit::MAX / 2);
        let die_msddigit_n =
            get_uniform_die(SDDigit::MIN / 2, SDDigit::MIN / 4);

        for i in i16::MIN..i16::MAX {
            let vec: Vec<SDDigit> = vec![
                die.sample(&mut rng),
                die_mdigit.sample(&mut rng),
                die_msddigit.sample(&mut rng),
                die_msddigit_n.sample(&mut rng),
                i as SDDigit,
                Digit::MAX as SDDigit + i as SDDigit,
            ];

            for x in vec {
                assert_eq!(!Arbi::from(x), !x);
            }
        }
    }
}
