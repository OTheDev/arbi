/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

//! Convert an `Arbi` object to an integral type T.
//!
//! As with the C++20 Standard (7.3.8, p. 93):
//! > [T]he result is the unique value of the destination type that is congruent
//! > to the source integer modulo \\( 2^{N} \\), where \\( N \\) is the width
//! > of the destination type.
//!
//! <https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions>
//! Casting from a larger integer to a smaller integer (e.g. u32 -> u8) will
//! truncate.

use crate::is_signed::IsSigned;
use crate::uints::div_ceil_usize;
use crate::{Arbi, Digit};

/* !impl_to_integral */
macro_rules! impl_to_integral {
    ($($t:ty => ($to_unchecked:ident, $to_checked:ident, $fits:ident)),*) => {
        $(

impl Arbi {
    /// Convert this [`Arbi`] integer to a primitive integer type value.
    ///
    /// This is "wrapping".
    ///
    /// # Note
    /// - `From<Arbi>` and `From<&Arbi>` are implemented for each primitive
    ///   integral type and has the same semantics. See, for example,
    ///   [`impl From<&Arbi> for i32`](#impl-From<%26Arbi>-for-i32).
    /// - In Rust, casting from a larger primitive integer type to a smaller
    ///   integer type truncates. This function has the same semantics.
    ///
    /// # Return
    /// Return the unique value of this target primitive integer type that is
    /// congruent to the [`Arbi`] integer, modulo \\( 2^{N} \\), where \\( N \\)
    /// is the width of the target type.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let x = Arbi::from(i32::MIN);
    /// let y: i32 = x.wrapping_to_i32();
    /// let z: i16 = x.wrapping_to_i16();
    /// assert_eq!(y, i32::MIN);
    /// assert_eq!(z, i32::MIN as i16);
    /// assert_eq!(i16::from(&x), i32::MIN as i16);
    /// ```
    pub fn $to_unchecked(&self) -> $t {
        type TargetT = $t;

        if self.size() == 0 {
            return 0;
        }

        const T_BITS: usize = TargetT::BITS as usize;
        const T_IS_SIGNED: bool = TargetT::IS_SIGNED;
        const T_BITS_IS_GT_DIGIT_BITS: bool = T_BITS > Digit::BITS as usize;

        let mut ret: TargetT = 0;

        if T_BITS_IS_GT_DIGIT_BITS {
            const MAX_DIGITS_FOR_T: usize =
                div_ceil_usize(T_BITS, Digit::BITS as usize);
            let n_digits: usize = self.size().min(MAX_DIGITS_FOR_T);

            for i in (0..n_digits).rev() {
                ret = if T_BITS_IS_GT_DIGIT_BITS {
                    (ret << Digit::BITS) | self.vec[i] as TargetT
                } else {
                    ((ret << Digit::BITS) as Digit | self.vec[i]) as TargetT
                };
            }
        } else {
            ret = self.vec[0] as TargetT;
        }

        if T_IS_SIGNED {
            if self.is_negative() {
                // ret = -ret;
                ret = (0 as TargetT).wrapping_sub(ret);
            }
        } else if self.is_negative() {
            ret = (!ret).wrapping_add(1);
        }

        ret
    }

    /// Convert this [`Arbi`] integer to a primitive integer type value.
    ///
    /// # Return
    /// `Some(value)` if the [`Arbi`] value fits within the target type's range,
    /// `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let x = Arbi::from(i32::MIN);
    /// let y = x.checked_to_i32();
    /// assert_eq!(y, Some(i32::MIN));
    /// let z = x.checked_to_i16();
    /// assert!(z.is_none());
    /// ```
    pub fn $to_checked(&self) -> Option<$t> {
        if self.$fits() {
            Some(self.$to_unchecked())
        } else {
            None
        }
    }

    /// Return `true` if this integer fits in this primitive integer type,
    /// `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let mut x = Arbi::from(u8::MAX);
    /// assert!(x.fits_u8());
    /// x.incr();
    /// assert!(!x.fits_u8());
    /// ```
    ///
    /// #
    pub fn $fits(&self) -> bool {
        type TargetT = $t;
        (&TargetT::MIN..=&TargetT::MAX).contains(&self)
    }
}

#[cfg(test)]
mod $to_unchecked {
    #[test]
    fn $to_unchecked() {
        use super::*;
        use crate::util::test::{
            get_seedable_rng, get_uniform_die, Distribution,
        };
        use crate::{QDigit, SQDigit};

        let mut arbi = Arbi::new();
        assert_eq!(0, arbi.$to_unchecked());
        assert_eq!(Some(0), arbi.$to_checked());

        arbi = Arbi::from(<$t>::MIN);
        assert_eq!(<$t>::MIN, arbi.$to_unchecked());
        assert_eq!(Some(<$t>::MIN), arbi.$to_checked());

        arbi = Arbi::from(<$t>::MAX);
        assert_eq!(<$t>::MAX, arbi.$to_unchecked());
        assert_eq!(Some(<$t>::MAX), arbi.$to_checked());

        if <$t>::BITS < 128 {
            // not i128 or u128
            arbi = Arbi::from((<$t>::MIN as i128).wrapping_sub(1));
            assert_eq!(
                ((<$t>::MIN as i128).wrapping_sub(1)) as $t,
                arbi.$to_unchecked()
            );
            assert_eq!(None, arbi.$to_checked());

            arbi = Arbi::from((<$t>::MAX as u128).wrapping_add(1));
            assert_eq!(
                ((<$t>::MAX as u128).wrapping_add(1)) as $t,
                arbi.$to_unchecked()
            );
            assert_eq!(None, arbi.$to_checked());
        }

        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(<$t>::MIN, <$t>::MAX);
        for _ in 0..i16::MAX {
            let rv: $t = die.sample(&mut rng);
            let arbi = Arbi::from(rv);

            assert_eq!(rv, arbi.$to_unchecked());
            assert_eq!(Some(rv), arbi.$to_checked());
        }

        if <$t>::BITS == 128 && !<$t>::IS_SIGNED {
            // u128
            let die = get_uniform_die(QDigit::MIN, QDigit::MAX);
            for _ in 0..i16::MAX {
                let rv: QDigit = die.sample(&mut rng);
                let arbi = Arbi::from(rv);

                assert_eq!(rv as $t, arbi.$to_unchecked());

                if (rv >= (<$t>::MIN as QDigit))
                    && (rv <= (<$t>::MAX as QDigit))
                {
                    assert!(arbi.$fits());
                    assert_eq!(Some(rv as $t), arbi.$to_checked());
                } else {
                    assert!(!arbi.$fits());
                    assert_eq!(None, arbi.$to_checked());
                }
            }
        } else {
            // other
            let die = get_uniform_die(SQDigit::MIN, SQDigit::MAX);
            for _ in 0..i16::MAX {
                let rv: SQDigit = die.sample(&mut rng);
                let arbi = Arbi::from(rv);

                assert_eq!(rv as $t, arbi.$to_unchecked());

                if (rv >= (<$t>::MIN as SQDigit))
                    && (rv <= (<$t>::MAX as SQDigit))
                {
                    assert!(arbi.$fits());
                    assert_eq!(Some(rv as $t), arbi.$to_checked());
                } else {
                    assert!(!arbi.$fits());
                    assert_eq!(None, arbi.$to_checked());
                }
            }
        }
    }
}

/// Equivalent to converting an `Arbi` integer to this type using its
/// corresponding `wrapping_to_*()` method. For example, see
/// [`Arbi::wrapping_to_u32()`].
///
/// Please note that `From<&Arbi>` is also implemented. See, for example,
/// [`impl From<&Arbi> for i32`](#impl-From<%26Arbi>-for-i32).
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(123456789); // 0b111010110111100110100010101
/// let a_clone = a.clone();
/// let b = u32::from(a);
/// assert_eq!(b, 123456789);
/// let c = u16::from(a_clone);
/// assert_eq!(c, 52501); // 0b1100110100010101
/// ```
impl From<Arbi> for $t {
    fn from(arbi: Arbi) -> Self {
        arbi.$to_unchecked()
    }
}

/// Equivalent to converting an `Arbi` integer to this type using its
/// corresponding `wrapping_to_*()` method. For example, see
/// [`Arbi::wrapping_to_u32()`].
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(123456789); // 0b111010110111100110100010101
/// let b = u32::from(&a);
/// assert_eq!(b, 123456789);
/// let c = u16::from(&a);
/// assert_eq!(c, 52501); // 0b1100110100010101
/// ```
impl From<&Arbi> for $t {
    fn from(arbi: &Arbi) -> Self {
        arbi.$to_unchecked()
    }
}

        )*
    };
}
/* impl_to_integral! */

impl_to_integral!(
    i8 => (wrapping_to_i8, checked_to_i8, fits_i8),
    i16 => (wrapping_to_i16, checked_to_i16, fits_i16),
    i32 => (wrapping_to_i32, checked_to_i32, fits_i32),
    i64 => (wrapping_to_i64, checked_to_i64, fits_i64),
    i128 => (wrapping_to_i128, checked_to_i128, fits_i128),
    isize => (wrapping_to_isize, checked_to_isize, fits_isize),
    u8 => (wrapping_to_u8, checked_to_u8, fits_u8),
    u16 => (wrapping_to_u16, checked_to_u16, fits_u16),
    u32 => (wrapping_to_u32, checked_to_u32, fits_u32),
    u64 => (wrapping_to_u64, checked_to_u64, fits_u64),
    u128 => (wrapping_to_u128, checked_to_u128, fits_u128),
    usize => (wrapping_to_usize, checked_to_usize, fits_usize)
);
