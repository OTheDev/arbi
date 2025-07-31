/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/// `a += &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a += &b;
/// assert_eq!(a, -1358023);
/// ```
impl<'a> AddAssign<&'a Arbi> for Arbi {
    fn add_assign(&mut self, other: &'a Arbi) {
        self.iadd(other);
    }
}

/// `a += b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a += b;
/// assert_eq!(a, -1358023);
/// ```
impl AddAssign<Arbi> for Arbi {
    fn add_assign(&mut self, mut other: Self) {
        if other.capacity() > self.capacity() {
            core::mem::swap(self, &mut other);
        }
        *self += &other;
    }
}

/// `a + b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = a + b;
/// assert_eq!(c, -1358023);
/// ```
impl Add<Arbi> for Arbi {
    type Output = Self;
    fn add(mut self, other: Self) -> Self {
        self += other;
        self
    }
}

/// `a + &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = a + &b;
/// assert_eq!(c, -1358023);
/// ```
impl<'a> Add<&'a Arbi> for Arbi {
    type Output = Self;
    fn add(mut self, other: &'a Arbi) -> Self {
        self += other;
        self
    }
}

/// `&a + b`
///
/// # Examples
/// ```
/// use arbi::{Arbi, Digit};
///
/// let a = Arbi::from(-123456);
/// let b = Arbi::from(1234567);
/// let b_cap = b.capacity();
/// let c = &a + b; // In this case, no memory allocation (b's memory is
///                 // used.
/// assert_eq!(c, 1111111);
/// assert_eq!(c.capacity(), b_cap);
///
/// let a = Arbi::from(-(Digit::MAX as i128));
/// let b = Arbi::from(-1234567);
/// let b_cap = b.capacity();
/// let c = &a + b; // In this case, memory allocation may or may not occur,
///                 // depending on b's capacity.
/// assert!(c.capacity() >= b_cap);
/// ```
impl Add<Arbi> for &Arbi {
    type Output = Arbi;
    fn add(self, mut other: Arbi) -> Arbi {
        other += self;
        other
    }
}

/// `&a + &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = &a + &b;
/// assert_eq!(c, -1358023);
/// ```
impl<'b> Add<&'b Arbi> for &Arbi {
    type Output = Arbi;
    fn add(self, other: &'b Arbi) -> Arbi {
        let mut ret;
        if self.size() <= other.size() {
            ret = Arbi::with_capacity_and_copy(other.size() + 1, other);
            ret += self;
        } else {
            ret = Arbi::with_capacity_and_copy(self.size() + 1, self);
            ret += other;
        }
        ret
    }
}

/// `a -= &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a -= &b;
/// assert_eq!(a, -1111111);
/// ```
impl<'a> SubAssign<&'a Arbi> for Arbi {
    fn sub_assign(&mut self, other: &'a Arbi) {
        self.isub(other);
    }
}

/// `a -= b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a -= b;
/// assert_eq!(a, -1111111);
/// ```
impl SubAssign for Arbi {
    fn sub_assign(&mut self, mut other: Self) {
        if self.capacity() >= other.capacity() {
            *self -= &other;
        } else {
            // -(other - self) = self - other
            core::mem::swap(self, &mut other);
            *self -= &other;
            self.negate_mut();
        }
    }
}

/// `a - b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let a_cap = a.capacity();
/// let b = Arbi::from(-123456);
/// let c = a - b; // no memory allocation
/// assert_eq!(c, -1111111);
/// assert_eq!(c.capacity(), a_cap);
/// ```
impl Sub<Arbi> for Arbi {
    type Output = Self;
    fn sub(mut self, other: Self) -> Self {
        self -= other;
        self
    }
}

/// `a - &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let a_cap = a.capacity();
/// let b = Arbi::from(-123456);
/// let c = a - &b; // no memory allocation
/// assert_eq!(c, -1111111);
/// assert_eq!(c.capacity(), a_cap);
/// ```
impl<'a> Sub<&'a Arbi> for Arbi {
    type Output = Self;
    fn sub(mut self, other: &'a Arbi) -> Self {
        self -= other;
        self
    }
}

/// `&a - b`
///
/// # Examples
/// ```
/// use arbi::{Arbi, Digit};
///
/// let a = Arbi::from(1234567);
/// let b = Arbi::from(123456);
/// let b_cap = b.capacity();
/// let c = &a - b; // In this case, no memory allocation (b's memory is
///                 // used.
/// assert_eq!(c, 1111111);
/// assert_eq!(c.capacity(), b_cap);
///
/// let a = Arbi::from(-(Digit::MAX as i128));
/// let b = Arbi::from(-1234567);
/// let b_cap = b.capacity();
/// let c = &a - b; // In this case, no memory allocation
/// assert_eq!(c.capacity(), b_cap);
/// ```
impl Sub<Arbi> for &Arbi {
    type Output = Arbi;
    fn sub(self, mut other: Arbi) -> Arbi {
        // a - b = -(b - a)
        other -= self;
        other.negate_mut();
        other
    }
}

/// `&a - &b`
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = &a - &b; // memory allocation
/// assert_eq!(c, -1111111);
/// ```
impl<'b> Sub<&'b Arbi> for &Arbi {
    type Output = Arbi;
    fn sub(self, other: &'b Arbi) -> Arbi {
        let mut ret;
        if self.size() <= other.size() {
            // -(other - self) = self - other
            ret = Arbi::with_capacity_and_copy(other.size(), other);
            ret -= self;
            ret.negate_mut();
        } else {
            ret = Arbi::with_capacity_and_copy(self.size(), self);
            ret -= other;
        }
        ret
    }
}
