/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::ops::RangeInclusive;

/// Test if an `Arbi` integer fits within the range of type `T`.
///
/// # Examples
/// Using the `Fits` trait directly:
/// ```
/// use arbi::{Arbi, Fits};
///
/// let a = Arbi::from(u128::MAX);
/// assert!(!u64::fits(&a));
/// assert!(u128::fits(&a));
/// ```
///
/// Indirectly via [`Arbi::fits()`]:
/// ```
/// use arbi::{Arbi, Fits};
///
/// let a = Arbi::from(u128::MAX);
/// assert!(!a.fits::<u64>());
/// assert!(a.fits::<u128>());
/// ```
pub trait Fits<T> {
    #[allow(dead_code)]
    fn fits(value: &Arbi) -> bool;
}

/* !impl_fits_for_integers */
macro_rules! impl_fits_for_integers {
    ($($t:ty)*) => ($(

impl Fits<$t> for $t {
    fn fits(value: &Arbi) -> bool {
        let range: RangeInclusive<$t> = <$t>::MIN..=<$t>::MAX;
        range.contains(value)
    }
}

    )*)
}
/* impl_fits_for_integers! */

impl_fits_for_integers! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }

impl Arbi {
    /// Return `true` if this `Arbi` integer fits in the range of the target
    /// type.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Fits};
    ///
    /// let mut x = Arbi::from(255);
    /// assert!(x.fits::<u8>());
    ///
    /// x.incr();
    ///
    /// assert!(!x.fits::<u8>());
    /// ```
    pub fn fits<T: Fits<T>>(&self) -> bool {
        T::fits(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::Assign;
    use crate::{DDigit, Digit, SDDigit, SDigit};

    #[test]
    fn test_fits_integral() {
        let mut x = Arbi::zero();

        assert!(x.fits::<u32>());

        x.assign(Digit::MAX);
        assert!(x.fits::<Digit>());
        assert!(!x.fits::<SDigit>());

        x += Arbi::one();
        assert!(!x.fits::<Digit>());

        x.assign(-(Digit::MAX as SDDigit));
        assert!(!x.fits::<Digit>());
        assert!(x.fits::<SDDigit>());

        x -= Arbi::one();
        assert!(x.fits::<SDDigit>());

        x.assign(DDigit::MAX);
        assert!(x.fits::<DDigit>());
        assert!(!x.fits::<Digit>());

        x.assign(i32::MAX);
        assert!(x.fits::<i32>());
        assert!(!x.fits::<i16>());
    }
}
