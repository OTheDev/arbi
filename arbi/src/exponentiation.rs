/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::Arbi;

/// Return `self` to the power `exponent`.
///
/// # Usage
/// ```
/// use arbi::{Arbi, Pow};
///
/// let mut a = Arbi::from(2);
///
/// // Raise an `Arbi` integer to the power of a `usize` (`u128` also supported,
/// // up to a certain range).
/// a = a.pow(125_usize);
/// assert_eq!(a, 1_u128 << 125);
///
/// // Raise an `Arbi` integer to the power of another `Arbi`
/// a = a.pow(Arbi::from(2));
/// assert_eq!(a, Arbi::from_str_radix(
///     "400000000000000000000000000000000000000000000000000000000000000",
///     16
/// ).unwrap());
/// a = a.pow(&Arbi::from(2));
/// assert_eq!(a, Arbi::from_str_radix(
///     "1000000000000000000000000000000000000000000000000000000000000000000000\
///      00000000000000000000000000000000000000000000000000000000",
///     16
/// ).unwrap());
/// ```
///
/// A sufficient condition for the left shift operation to lead to exhaustion
/// of the internal digit vector's maximum capacity is that base is at least 2
/// in absolute value and that the exponent is greater than or equal to
/// [`Arbi::MAX_BITS`] (a value greater than `usize::MAX`). Rather than allow
/// programs to run a computation that is guaranteed to run out of memory,
/// programs will panic if these conditions are met:
/// ```should_panic
/// use arbi::{Arbi, Pow};
///
/// let mut a = Arbi::from(Arbi::MAX_BITS);
/// let mut one = Arbi::neg_one();
/// let mut two = Arbi::from(2);
///
/// one = one.pow(&a); // Ok
/// assert_eq!(one, 1);
///
/// two = two.pow(&a); // Panics
/// ```
///
/// Negative exponents will panic:
/// ```should_panic
/// use arbi::{Arbi, Pow};
///
/// let mut a = Arbi::from(2);
/// a = a.pow(Arbi::from(-10));
/// ```
pub trait Pow<T> {
    /// The return type of `pow()`.
    type Output;
    ///  Return `self` to the power `exponent`.
    fn pow(self, exponent: T) -> Self::Output;
}

pub(crate) trait PowAssign<T> {
    #[allow(dead_code)]
    fn pow_assign(&mut self, exponent: T);
}

impl Pow<usize> for Arbi {
    type Output = Self;

    fn pow(self, exp: usize) -> Arbi {
        (&self).pow(exp)
    }
}

impl<'a> Pow<&'a usize> for Arbi {
    type Output = Self;

    fn pow(self, exp: &'a usize) -> Arbi {
        self.pow(*exp)
    }
}

impl<'a> Pow<&'a usize> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: &'a usize) -> Arbi {
        if *exp == 0 {
            return 1.into();
        }

        if self == 0 || self == 1 {
            return self.clone();
        }
        if self == -1 {
            return if exp % 2 == 0 { 1.into() } else { (-1).into() };
        }

        // Guard against attempts to exponentiate when we know it will lead to
        // vectors max capacity to be exceeded. If base == 2 and exp > 0, the
        // result of 2 ** exp will have a bit length of exp + 1 bits. Big
        // integers are constrained such that their bit length is less than or
        // equal to MAX_BITS. Thus, we require that (exp + 1 <= MAX_BITS) <==>
        // (exp <= MAX_BITS - 1).
        if *exp as u128 >= Arbi::MAX_BITS {
            panic!(
                "This exponentiation operation will require a capacity greater \
                 than the maximum allowed for Vec."
            );
        }

        Arbi::exponentiation_left_to_right_usize(self, *exp)
    }
}

impl Pow<usize> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: usize) -> Arbi {
        self.pow(&exp)
    }
}

impl Pow<Arbi> for Arbi {
    type Output = Arbi;

    fn pow(self, exp: Arbi) -> Arbi {
        (&self).pow(&exp)
    }
}

impl<'a> Pow<&'a Arbi> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: &'a Arbi) -> Arbi {
        if exp < 0 {
            panic!("Negative exponents are not allowed.");
        }
        if exp == 0 {
            return 1.into();
        }

        if *self == 0 || *self == 1 {
            return self.clone();
        }
        if *self == -1 {
            return if exp.is_even() { 1.into() } else { (-1).into() };
        }

        // Guard against attempts to exponentiate when we know it will lead to
        // vectors max capacity to be exceeded. If base == 2 and exp > 0, the
        // result of 2 ** exp will have a bit length of exp + 1 bits. Big
        // integers are constrained such that their bit length is less than or
        // equal to MAX_BITS. Thus, we require that (exp + 1 <= MAX_BITS) <==>
        // (exp <= MAX_BITS - 1).
        if exp >= Arbi::MAX_BITS {
            panic!(
                "This exponentiation operation will require a capacity greater \
                 than the maximum allowed for Vec."
            );
        }

        Arbi::exponentiation_left_to_right_u128(
            self,
            match exp.checked_to_u128() {
                Some(val) => val,
                None => panic!("Exponent does not fit in a u128."),
            },
        )
    }
}

impl Pow<Arbi> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: Arbi) -> Arbi {
        self.pow(&exp)
    }
}

impl<'a> Pow<&'a Arbi> for Arbi {
    type Output = Arbi;

    fn pow(self, exp: &'a Arbi) -> Arbi {
        (&self).pow(exp)
    }
}

impl Arbi {
    fn exponentiation_left_to_right_usize(base: &Self, exp: usize) -> Arbi {
        assert!(exp > 0);
        // (1)
        let mut ret = Arbi::one();
        // (2)
        for j in (0..usize::bit_length(exp)).rev() {
            ret = &ret * &ret; // TODO: eff.
                               // Test if j-th bit of exp is set
            if (exp & ((1_usize) << j)) != 0 {
                ret *= base;
            }
        }
        // (3)
        ret
    }

    fn exponentiation_left_to_right_u128(base: &Self, exp: u128) -> Arbi {
        assert!(exp > 0);
        let mut ret = Arbi::one();
        for j in (0..u128::bit_length(exp)).rev() {
            ret = &ret * &ret;
            if (exp & ((1_u128) << j)) != 0 {
                ret *= base;
            }
        }
        ret
    }
}

impl Pow<u128> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: u128) -> Arbi {
        if exp == 0 {
            return 1.into();
        }
        if self == 0 || self == 1 {
            return self.clone();
        }
        if self == -1 {
            return if exp % 2 == 0 { 1.into() } else { (-1).into() };
        }
        if exp >= Arbi::MAX_BITS {
            panic!(
                "This exponentiation operation will require a capacity greater \
                 than the maximum allowed for Vec."
            );
        }
        Arbi::exponentiation_left_to_right_u128(self, exp)
    }
}

impl Pow<&u128> for &Arbi {
    type Output = Arbi;

    fn pow(self, exp: &u128) -> Arbi {
        self.pow(*exp)
    }
}

impl Pow<u128> for Arbi {
    type Output = Arbi;

    fn pow(self, exp: u128) -> Arbi {
        (&self).pow(exp)
    }
}

impl Pow<&u128> for Arbi {
    type Output = Arbi;

    fn pow(self, exp: &u128) -> Arbi {
        (&self).pow(*exp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DDigit;
    use crate::SDDigit;

    #[test]
    fn zero_base() {
        let zero = Arbi::zero();
        assert_eq!((&zero).pow(9_usize), 0);
        assert_eq!(
            (&zero).pow(
                Arbi::from_str_base("987654321", 10.try_into().unwrap())
                    .unwrap()
            ),
            0
        );
    }

    #[test]
    fn zero_exponent() {
        let (zero, ddmax, sdmin) = (
            Arbi::zero(),
            Arbi::from(DDigit::MAX),
            Arbi::from(SDDigit::MIN),
        );

        assert_eq!((&zero).pow(0_usize), 1);
        assert_eq!((&ddmax).pow(0_usize), 1);
        assert_eq!((&sdmin).pow(0_usize), 1);
    }

    #[test]
    #[should_panic]
    fn negative_exponent_zero_base() {
        let zero = Arbi::zero();
        zero.pow(Arbi::neg_one());
    }

    #[test]
    #[should_panic]
    fn negative_exponent_ddmax_base() {
        let ddmax = Arbi::from(DDigit::MAX);
        ddmax.pow(Arbi::from(-9));
    }

    #[test]
    #[should_panic]
    fn negative_exponent_sdmin_base() {
        let sdmin = Arbi::from(SDDigit::MIN);
        sdmin.pow(
            Arbi::from_str_base("-90932093239", 10.try_into().unwrap())
                .unwrap(),
        );
    }

    // Should keep negative
    #[test]
    fn negative_base_odd_exponent() {
        let mone = Arbi::neg_one();
        let sdmin = Arbi::from(SDDigit::MIN);

        assert_eq!((&mone).pow(1_usize), -1);
        assert_eq!((&mone).pow(3_usize), -1);
        assert_eq!(sdmin.pow(23_usize), Arbi::from_str_base(
            "-15576278982380581948964421084138746384406111591549949945834451458\
              98846278001462648694944985132025705960729951317997322375288085047\
              51642692883400082761745423666832428490143668329212201902149561345\
              71925165639489309943923815222597869534386036689228554339277123009\
              45575766753370369126991084298521781809546945499265389499472871267\
              85452396817731616331124975854625984987279633462629005911338101835\
              94348131919182810880788041032667027313956749312",
             10.try_into().unwrap()
        ).unwrap());
    }

    // Should make positive
    #[test]
    fn negative_base_even_exponent() {
        let mone = Arbi::neg_one();
        let sdmin = Arbi::from(SDDigit::MIN);

        assert_eq!((&mone).pow(2_usize), 1);
        assert_eq!((&mone).pow(4_usize), 1);
        assert_eq!(sdmin.pow(28_usize), Arbi::from_str_base(
            "103971031169538340124421817778820199111807322258375679185982614564\
             906679570155216302611344072176463723871679899611535689744781108885\
             100968176394849634330641511076243696694611537005274036323602361682\
             111083622989307588713647881955005902365403198712787692241264106282\
             524778965725571285894134892811769755532844845186085380730463982943\
             416543952650637325731574188048519119499346987358986072148040002877\
             450262263363146478527498944936048377329839250155330892874094061087\
             045864641276073782007832859619538558324648025212157435161184191486\
             3616",
            10.try_into().unwrap()
        ).unwrap());
    }

    #[test]
    fn guard_branch_for_arbi_with_arbi_overload() {
        let (zero, one, mone) = (Arbi::zero(), Arbi::one(), Arbi::neg_one());
        let max_bits = Arbi::from(Arbi::MAX_BITS);
        let max_bits_plus_one = Arbi::from(Arbi::MAX_BITS + 1);

        assert_eq!(zero.pow(&max_bits), 0);
        assert_eq!(one.pow(&max_bits), 1);
        assert_eq!((&mone).pow(&max_bits), 1); // even
        assert_eq!((&mone).pow(&max_bits_plus_one), -1); // odd
    }

    #[test]
    #[should_panic]
    fn guard_branch_for_arbi_with_arbi_overload_should_panic() {
        let two = Arbi::from(2);
        two.pow(Arbi::from(Arbi::MAX_BITS));
    }

    #[test]
    #[should_panic]
    fn guard_branch_for_arbi_with_arbi_overload_should_panic_p1() {
        let two = Arbi::from(2);
        two.pow(Arbi::from(Arbi::MAX_BITS + 1));
    }
}
