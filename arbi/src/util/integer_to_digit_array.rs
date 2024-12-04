/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

#[allow(dead_code)]
pub(crate) trait ToDigitArray<const N: usize> {
    fn to_digit_array(&self) -> Option<([Digit; N], usize)>;
}

/* !impl_to_digit_array_for_uint */
macro_rules! impl_to_digit_array_for_uint {
    // One digit
    ($t:ty, 1) => {
        impl ToDigitArray<1> for $t {
            fn to_digit_array(&self) -> Option<([Digit; 1], usize)> {
                if *self == 0 {
                    return None;
                }
                let digit = [(*self & Digit::MAX as $t) as Digit];
                Some((digit, 1))
            }
        }
    };
    // More than one digit
    ($t:ty, $digits:expr) => {
        impl ToDigitArray<$digits> for $t {
            fn to_digit_array(&self) -> Option<([Digit; $digits], usize)> {
                if *self == 0 {
                    return None;
                }
                let mut uvalue = *self;
                let mut digits = [0; $digits];
                let mut index = 0;
                while uvalue != 0 && index < $digits {
                    digits[index] = uvalue as Digit;
                    uvalue >>= Digit::BITS;
                    index += 1;
                }
                Some((digits, index))
            }
        }
    };
}
/* impl_to_digit_array_for_uint! */

impl_to_digit_array_for_uint!(u8, 1);
impl_to_digit_array_for_uint!(u16, 1);
impl_to_digit_array_for_uint!(u32, 1);
impl_to_digit_array_for_uint!(u64, 2);
impl_to_digit_array_for_uint!(u128, 4);
impl_to_digit_array_for_uint!(usize, {
    ((Digit::BITS + (usize::BITS - 1)) / usize::BITS) as usize
});

impl Arbi {
    #[allow(dead_code)]
    fn from_unsigned<T: ToDigitArray<D>, const D: usize>(n: T) -> Self {
        if let Some((digits, size)) = n.to_digit_array() {
            Arbi {
                vec: digits[..size].to_vec(),
                neg: false,
            }
        } else {
            Arbi::zero()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit, QDigit};
    use alloc::vec;

    #[test]
    fn test_to_digit_array_zero() {
        assert_eq!(0u32.to_digit_array(), None);
    }

    #[test]
    fn test_smoke() {
        let (mut rng, _) = get_seedable_rng();

        let die_u8 = get_uniform_die(1, u8::MAX);
        let die_u16 = get_uniform_die(1, u16::MAX);
        let die_digit = get_uniform_die(1, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_u8.sample(&mut rng);
            let a = Arbi::from(r);
            let expected = Some((a.vec.clone().try_into().unwrap(), a.size()));
            assert_eq!(r.to_digit_array(), expected);

            let r = die_u16.sample(&mut rng);
            let a = Arbi::from(r);
            let expected = Some((a.vec.clone().try_into().unwrap(), a.size()));
            assert_eq!(r.to_digit_array(), expected);

            let r = die_digit.sample(&mut rng);
            let a = Arbi::from(r);
            let expected = Some((a.vec.clone().try_into().unwrap(), a.size()));
            assert_eq!(r.to_digit_array(), expected);

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            let expected = Some((a.vec.clone().try_into().unwrap(), a.size()));
            assert_eq!(r.to_digit_array(), expected);

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            let expected = Some((a.vec.clone().try_into().unwrap(), a.size()));
            assert_eq!(r.to_digit_array(), expected);
        }
    }

    #[test]
    fn test_arbi_from_unsigned_basic() {
        let a = Arbi::from_unsigned(257u32);
        assert_eq!(a.vec, vec![257]);

        let zero = Arbi::from_unsigned(0u32);
        assert!(zero.vec.is_empty());
    }
}
