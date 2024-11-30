/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! From ISO/IEC 2020 (C++), "[t]he value of `E1 >> E2` is `E1/2^{E2}, rounded
//! down. [Note: E1 is right-shifted E2 bit positions. Right-shift on signed
//! integral types is an arithmetic right shift, which performs sign-extension.
//! —end note]".
//!
//! In Rust, >> is also an arithmetic right shift on signed integer types.

use crate::{Arbi, DDigit, Digit};
use core::ops::{Shr, ShrAssign};

impl Arbi {
    fn right_shift_inplace(&mut self, n_bits: usize) {
        let mut dig_shift: usize = n_bits / (Digit::BITS as usize);
        let mut bit_shift: usize = n_bits % (Digit::BITS as usize);

        if self.negative() && bit_shift == 0 {
            if dig_shift == 0 {
                return;
            } else {
                bit_shift = Digit::BITS as usize;
                dig_shift -= 1;
            }
        }

        let size_self = self.size();

        if size_self <= dig_shift {
            if self.negative() {
                self.make_one(true);
            } else {
                self.make_zero();
            }
            return;
        }

        let size = size_self - dig_shift;

        self.vec.truncate(size + 1);
        let compl_bit_shift = (Digit::BITS as usize) - bit_shift;

        let mut s: DDigit = self.vec[dig_shift] as DDigit;
        if self.negative() {
            self.vec.truncate(size);

            let mut d: Digit = 0;
            for i in 0..dig_shift {
                d |= self.vec[i];
            }
            s += (if d != 0 { 1 as Digit } else { 0 as Digit }
                + (Digit::MAX >> compl_bit_shift)) as DDigit;
        }

        s >>= bit_shift;
        for (i, j) in ((dig_shift + 1)..size_self).enumerate() {
            s += (self.vec[j] as DDigit) << compl_bit_shift;
            self.vec[i] = s as Digit;
            s >>= Digit::BITS;
        }

        self.vec[size - 1] = s as Digit;
        self.vec.truncate(size);
        self.trim();
    }
}

/// Return a new integer representing this integer right-shifted `rhs` bit
/// positions. This is an arithmetic right shift with sign extension.
///
/// Mathematically, the value of the resulting integer is \\(
/// \frac{x}{2^{\text{shift}}} \\), rounded down:
/// \\[
///     \left\lfloor \frac{x}{2^{\text{shift}}} \right\rfloor
/// \\]
/// where \\( x \\) is the big integer.
///
/// This is consistent with Rust's built-in behavior for right shifting
/// primitive integer type values.
///
/// # Note
/// Currently, when right-shifting a reference to an `Arbi` (`&Arbi`), the
/// operation involves cloning the `Arbi` integer, which incurs memory
/// allocation. To avoid these allocations, prefer using the in-place
/// right-shift operator `>>=` on a mutable reference (`&mut Arbi`), or the
/// move-based right-shift operator `>>` on an `Arbi` instance.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let mut a = Arbi::from(-987654321);
/// // In-place
/// a >>= 1;
/// assert_eq!(a, -493827161);
///
/// // Also in-place
/// a = a >> 1;
/// assert_eq!(a, -246913581);
///
/// // Clones the Arbi integer
/// a = &a >> 1;
/// assert_eq!(a, -123456791);
/// ```
///
/// ## Complexity
/// \\( O(n) \\)
impl Shr<usize> for &Arbi {
    type Output = Arbi;

    fn shr(self, rhs: usize) -> Self::Output {
        let mut ret = self.clone();
        Arbi::right_shift_inplace(&mut ret, rhs);
        ret
    }
}

/// See [`impl Shr<usize> for &Arbi`](#impl-Shr<usize>-for-%26Arbi).
impl Shr<usize> for Arbi {
    type Output = Arbi;

    fn shr(mut self, rhs: usize) -> Self::Output {
        Self::right_shift_inplace(&mut self, rhs);
        self
    }
}

/// See [`impl Shr<usize> for &Arbi`](#impl-Shr<usize>-for-%26Arbi).
impl ShrAssign<usize> for Arbi {
    fn shr_assign(&mut self, rhs: usize) {
        Self::right_shift_inplace(self, rhs);
    }
}

/// See [`impl Shr<usize> for &Arbi`](#impl-Shr<usize>-for-%26Arbi).
impl ShrAssign<&usize> for Arbi {
    fn shr_assign(&mut self, rhs: &usize) {
        Self::right_shift_inplace(self, *rhs);
    }
}

/// See [`impl Shr<usize> for &Arbi`](#impl-Shr<usize>-for-%26Arbi).
impl<'a> Shr<&'a usize> for &Arbi {
    type Output = Arbi;

    fn shr(self, rhs: &'a usize) -> Self::Output {
        let mut ret = self.clone();
        Arbi::right_shift_inplace(&mut ret, *rhs);
        ret
    }
}

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit, SDDigit};

    #[test]
    fn right_shift_assign() {
        let mut zero = Arbi::zero();
        zero >>= 1;
        assert_eq!(zero, 0);

        let mut a = Arbi::from(Digit::MAX as DDigit * 2);
        a >>= Digit::BITS as usize;
        assert_eq!(a, 1);

        let mut a = Arbi::from(3619132862646584885328_u128);
        a >>= 1;
        assert_eq!(a, 1809566431323292442664_u128);
        a >>= 21;
        assert_eq!(a, 862868514691969_u64);
        a >>= 50;
        assert_eq!(a, 0);

        let mut a = Arbi::from(16);
        a >>= 3;
        assert_eq!(a, 2);

        let mut a = Arbi::from(4);
        a >>= 4;
        assert_eq!(a, 0);
    }

    #[test]
    fn right_shift() {
        assert_eq!(Arbi::zero() >> 1, 0);
        assert_eq!(
            Arbi::from(Digit::MAX as DDigit * 2) >> Digit::BITS as usize,
            1
        );
        assert_eq!(
            Arbi::from_str_base(
                "3619132862646584885328",
                10.try_into().unwrap()
            )
            .unwrap()
                >> 1,
            Arbi::from_str_base(
                "1809566431323292442664",
                10.try_into().unwrap()
            )
            .unwrap()
        );

        let pos = Arbi::from(16);
        assert_eq!(&pos >> 3, 2);
        assert_eq!(&pos >> 0, 16);
        assert_eq!(&pos >> (Digit::BITS * 2) as usize, 0);

        let neg = Arbi::from(-16);
        assert_eq!(&neg >> 2, -4);
        assert_eq!(&neg >> 0, -16);
        assert_eq!(&neg >> (Digit::BITS * 2) as usize, -1);

        let mon = Arbi::from(-1);
        assert_eq!(&mon >> 0, -1);
        assert_eq!((&mon) >> 1, -1);
        assert_eq!(&mon >> (Digit::BITS + 1) as usize, -1);
    }

    #[test]
    fn right_shift_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for i in i16::MIN..i16::MAX {
            let r: SDDigit = die.sample(&mut rng);

            for shift in 0..=((2 * Digit::BITS as usize) - 1) {
                assert_eq!(
                    Arbi::from(r) >> shift,
                    r >> shift,
                    "Shift = {}, r = {}, Arbi = {}, i = {}",
                    shift,
                    r,
                    Arbi::from(r) >> shift,
                    i
                );
            }
        }
    }
}
