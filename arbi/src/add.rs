/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::{Arbi, Digit};
use core::ops::{Add, AddAssign, Sub, SubAssign};

impl Arbi {
    /// Set \\( self = |self| + |y| \\).
    fn add_abs_inplace(&mut self, y: &Self) {
        let max_size = self.size().max(y.size());
        self.vec.resize(max_size + 1, 0);
        let mut temp: Digit = 0;
        let mut carry: u8 = 0;
        for i in 0..y.size() {
            Digit::uaddc(&mut temp, self.vec[i], y.vec[i], &mut carry);
            self.vec[i] = temp;
        }
        for i in y.size()..max_size {
            temp = self.vec[i].wrapping_add(carry as Digit);
            carry = if temp < carry as Digit { 1 } else { 0 };
            self.vec[i] = temp;
        }
        self.vec[max_size] = carry as Digit;
        self.trim();
        self.neg = false;
    }

    /// \\( self += y \\)
    fn add_inplace(&mut self, y: &Self) {
        if self.is_negative() {
            if y.is_negative() {
                // x < 0, y < 0 ==> x = -|x|, y = -|y|. ==> x + y = -(|x| + |y|)
                self.add_abs_inplace(y); // this is never zero
                self.neg = true;
            } else {
                // x < 0, y >= 0 ==> x = -|x|, y = |y| ==> x + y = |y| - |x|
                self.sub_abs_inplace(y, true);
            }
        } else if y.is_negative() {
            // x >= 0, y < 0 ==> x = |x|, y = -|y| ==> x + y = |x| - |y|
            self.sub_abs_inplace(y, false);
        } else {
            // x >= 0, y >= 0 ==> x = |x|, y = |y| ==> x + y = |x| + |y|
            self.add_abs_inplace(y);
        }
    }

    fn resize_and_sub_abs_from_larger(&mut self, other: &Self) {
        self.vec.resize(other.size(), 0);
        let mut temp: Digit = 0;
        let mut borrow: u8 = 0;
        for i in 0..self.size() {
            Digit::usubb(&mut temp, other.vec[i], self.vec[i], &mut borrow);
            self.vec[i] = temp;
        }
        self.trim();
    }

    /// Set \\( x = |x| - |y| \\), assuming \\( |x| > |y| \\).
    fn sub_abs_gt_inplace(&mut self, y: &Self) {
        let mut temp: Digit = 0;
        let mut borrow: u8 = 0;
        for i in 0..y.size() {
            Digit::usubb(&mut temp, self.vec[i], y.vec[i], &mut borrow);
            self.vec[i] = temp;
        }
        for i in y.size()..self.size() {
            temp = self.vec[i].wrapping_sub(borrow as Digit);
            borrow = if temp > self.vec[i] { 1 } else { 0 };
            self.vec[i] = temp;
        }
        self.trim();
        self.neg = false;
    }

    /// \\( self -= y \\) if `from_other` is `false`.
    /// \\( self = y - self \\) if `from_other` is `true`.
    fn sub_inplace(&mut self, y: &Self, from_other: bool) {
        if self.is_negative() {
            if y.is_negative() {
                // x < 0, y < 0 ==> x = -|x|, y = -|y| ==> x - y = |y| - |x|
                self.sub_abs_inplace(y, !from_other);
            } else {
                // x < 0, y >= 0 ==> x = -|x|, y = |y| ==> x - y = -(|x| + |y|)
                self.add_abs_inplace(y);
                self.neg = true;
            }
        } else if y.is_negative() {
            // x >= 0, y < 0 ==> x = |x|, y = -|y| ==> x - y = |x| + |y|
            self.add_abs_inplace(y);
        } else {
            // x >= 0, y >= 0 ==> x = |x|, y = |y| ==> x - y = |x| - |y|
            self.sub_abs_inplace(y, from_other);
        }
    }

    /// Set \\( x = |x| - |y| \\).
    pub(crate) fn sub_abs_inplace(&mut self, y: &Self, from_other: bool) {
        match self.size().cmp(&y.size()) {
            core::cmp::Ordering::Equal => {
                let it_self = self.vec.iter().rev();
                let mut it_y = y.vec.iter().rev();
                // Find the first mismatch
                let mismatch = it_self.zip(it_y.by_ref()).find(|(a, b)| a != b);
                if mismatch.is_none() {
                    // x, y have the same digits (or both are zero)
                    self.vec.clear();
                    self.neg = false;
                    return;
                }
                let (first_mismatched_self, first_mismatched_y) =
                    mismatch.unwrap();

                if first_mismatched_y > first_mismatched_self {
                    self.resize_and_sub_abs_from_larger(y);
                    self.neg = !from_other;
                } else {
                    self.sub_abs_gt_inplace(y);
                    self.neg = from_other;
                }
            }
            core::cmp::Ordering::Greater => {
                self.sub_abs_gt_inplace(y);
                self.neg = from_other;
            }
            core::cmp::Ordering::Less => {
                self.resize_and_sub_abs_from_larger(y);
                self.neg = !from_other;
            }
        }
    }
}

/// Implements `self + rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = a + b;
/// assert_eq!(c, -1358023);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl Add<Arbi> for Arbi {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        self.add_(other)
    }
}

/// Implements `self + &rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = a + &b;
/// assert_eq!(c, -1358023);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl<'a> Add<&'a Arbi> for Arbi {
    type Output = Self;

    fn add(mut self, other: &'a Arbi) -> Self {
        self.add_mut(other);
        self
    }
}

/// Implements `&self + &rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = &a + &b;
/// assert_eq!(c, -1358023);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl<'b> Add<&'b Arbi> for &Arbi {
    type Output = Arbi;

    fn add(self, other: &'b Arbi) -> Arbi {
        self.add_ref(other)
    }
}

/// Implements `&self + rhs`.
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
///
/// # Complexity
/// \\( O(n) \\)
impl Add<Arbi> for &Arbi {
    type Output = Arbi;

    fn add(self, mut other: Arbi) -> Arbi {
        other.add_mut(self);
        other
    }
}

/// Implements `self += rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a += b;
/// assert_eq!(a, -1358023);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl AddAssign for Arbi {
    fn add_assign(&mut self, mut other: Self) {
        self.add_mut_swap(&mut other);
    }
}

/// Implements `self += &rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a += &b;
/// assert_eq!(a, -1358023);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl<'a> AddAssign<&'a Arbi> for Arbi {
    fn add_assign(&mut self, other: &'a Arbi) {
        self.add_mut(other);
    }
}

/// Implements `self - rhs`.
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
///
/// # Complexity
/// \\( O(n) \\)
impl Sub<Arbi> for Arbi {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self.sub_(other)
    }
}

/// Implements `self - &rhs`.
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
///
/// # Complexity
/// \\( O(n) \\)
impl<'a> Sub<&'a Arbi> for Arbi {
    type Output = Self;

    fn sub(mut self, other: &'a Arbi) -> Self {
        self.sub_mut(other);
        self
    }
}

/// Implements `&self - &rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// let c = &a - &b; // memory allocation
/// assert_eq!(c, -1111111);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl<'b> Sub<&'b Arbi> for &Arbi {
    type Output = Arbi;

    fn sub(self, other: &'b Arbi) -> Arbi {
        self.sub_ref(other)
    }
}

/// Implements `&self - rhs`.
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
///
/// # Complexity
/// \\( O(n) \\)
impl Sub<Arbi> for &Arbi {
    type Output = Arbi;

    fn sub(self, mut other: Arbi) -> Arbi {
        // Set other to self - other, in-place if there's enough capacity.
        other.sub_mut_(self, true);
        other
    }
}

/// Implements `self -= rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a -= b;
/// assert_eq!(a, -1111111);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl SubAssign for Arbi {
    fn sub_assign(&mut self, mut other: Self) {
        self.sub_mut_swap(&mut other);
    }
}

/// Implements `self -= &rhs`.
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(-1234567);
/// let b = Arbi::from(-123456);
/// a -= &b;
/// assert_eq!(a, -1111111);
/// ```
///
/// # Complexity
/// \\( O(n) \\)
impl<'a> SubAssign<&'a Arbi> for Arbi {
    fn sub_assign(&mut self, other: &'a Arbi) {
        self.sub_mut(other);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, SDDigit, SDigit};

    #[test]
    fn test_add() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let zero = Arbi::default();

        assert_eq!(&a + &b, 5);
        assert_eq!(&b + &a, 5);
        assert_eq!(&a + &zero, 10);
        assert_eq!(&zero + &a, 10);
        assert_eq!(&b + &zero, -5);
        assert_eq!(&zero + &b, -5);
        assert_eq!(&a + &a, 20);
        assert_eq!(&b + &b, -10);

        // Important edge case
        let c = Arbi::from(DDigit::MAX);
        let d = c.clone();

        assert_eq!(d + c, 36893488147419103230_u128);
    }

    #[test]
    fn test_add_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) =
                (die_sd.sample(&mut rng), die_sd.sample(&mut rng));
            let (mut a, b) = (Arbi::from(a_in), Arbi::from(b_in));

            assert_eq!(&a + &b, a_in as SDDigit + b_in as SDDigit);

            a += b;
            assert_eq!(a, a_in as SDDigit + b_in as SDDigit)
        }
    }

    #[test]
    fn test_sub() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let z = Arbi::zero();

        assert_eq!(&a - &b, 15);
        assert_eq!(&b - &a, -15);
        assert_eq!(&a - &z, 10);
        assert_eq!(&z - &a, -10);
        assert_eq!(&z - &b, 5);
        assert_eq!(&b - &z, -5);
        assert_eq!(&a - &a, 0);
        assert_eq!(&b - &b, 0);
    }

    #[test]
    fn test_sub_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) =
                (die_sd.sample(&mut rng), die_sd.sample(&mut rng));
            let (mut a, b) = (Arbi::from(a_in), Arbi::from(b_in));

            assert_eq!(&a - &b, a_in as SDDigit - b_in as SDDigit);

            a -= &b;
            assert_eq!(a, a_in as SDDigit - b_in as SDDigit);
        }
    }

    #[test]
    fn test_add_assign() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);
        a += &b;
        assert_eq!(a, 5);

        let mut a = Arbi::from(99090);
        let b = Arbi::from(9909032932_u64);
        a += &b;
        assert_eq!(a, 9909132022_u64);

        let mut c = Arbi::from(7);
        c += c.clone(); // Can't do c += &c
        assert_eq!(c, 14);
    }

    #[test]
    fn test_sub_assign() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);
        a -= &b;
        assert_eq!(a, 15);
        assert_eq!(b, -5);

        let mut c = Arbi::from(7);
        c -= c.clone(); // Can't do c -= &c
        assert_eq!(c, 0);
    }
}

#[allow(dead_code)]
impl Arbi {
    /// Return \\( self + rhs \\).
    pub(crate) fn add_(mut self, mut rhs: Arbi) -> Arbi {
        if rhs.capacity() > self.capacity() {
            rhs.add_mut(&self);
            rhs
        } else {
            self.add_mut(&rhs);
            self
        }
    }

    /// \\( self = self + rhs \\)..
    pub(crate) fn add_mut(&mut self, rhs: &Self) -> &mut Self {
        self.add_inplace(rhs);
        self
    }

    /// \\( self = self + rhs \\) and `rhs` may be unchanged or equal to `self`,
    /// depending if `self.capacity >= rhs.capacity` or not.
    pub(crate) fn add_mut_swap(&mut self, rhs: &mut Self) -> &mut Self {
        if rhs.capacity() > self.capacity() {
            core::mem::swap(self, rhs);
        }
        self.add_mut(rhs);
        self
    }

    /// Return \\( self + rhs \\).
    pub(crate) fn add_ref(&self, rhs: &Self) -> Arbi {
        // Ensure only one allocation.
        if rhs.size() > self.size() {
            let mut ret = Arbi::with_capacity_and_copy(rhs.size() + 1, rhs);
            ret.add_mut(self);
            ret
        } else {
            let mut ret = Arbi::with_capacity_and_copy(self.size() + 1, self);
            ret.add_mut(rhs);
            ret
        }
    }

    /// Return \\( |self| + |rhs|` \\).
    pub(crate) fn add_abs(mut self, mut rhs: Arbi) -> Arbi {
        if rhs.capacity() > self.capacity() {
            rhs.add_abs_mut(&self);
            rhs
        } else {
            self.add_abs_mut(&rhs);
            self
        }
    }

    /// \\( self = |self| + |rhs| \\).
    pub(crate) fn add_abs_mut(&mut self, rhs: &Arbi) -> &mut Arbi {
        self.add_abs_inplace(rhs);
        self
    }

    /// \\( self = |self| + |rhs| \\) and `rhs` may be unchanged or equal to
    /// `self`, depending if `self.capacity >= rhs.capacity` or not.
    pub(crate) fn add_abs_mut_swap(&mut self, rhs: &mut Arbi) -> &mut Arbi {
        if rhs.capacity() > self.capacity() {
            core::mem::swap(self, rhs);
        }
        self.add_abs_mut(rhs);
        self
    }

    /// Return \\( |self| + |rhs| \\).
    pub(crate) fn add_abs_ref(&self, rhs: &Arbi) -> Arbi {
        // Ensure only one allocation.
        if rhs.size() > self.size() {
            let mut ret = Arbi::with_capacity_and_copy(rhs.size() + 1, rhs);
            ret.add_abs_mut(self);
            ret
        } else {
            let mut ret = Arbi::with_capacity_and_copy(self.size() + 1, self);
            ret.add_abs_mut(rhs);
            ret
        }
    }

    /// Return \\( self - rhs \\).
    pub(crate) fn sub_(mut self, mut rhs: Arbi) -> Arbi {
        if rhs.capacity() > self.capacity() {
            // self - rhs = -(rhs - self)
            rhs.sub_mut(&self);
            rhs.negate_mut();
            rhs
        } else {
            self.sub_mut(&rhs);
            self
        }
    }

    /// \\( self = self - rhs \\).
    pub(crate) fn sub_mut(&mut self, rhs: &Self) -> &mut Self {
        self.sub_mut_(rhs, false)
    }

    /// \\( self = self - rhs \\).
    pub(crate) fn sub_mut_(
        &mut self,
        rhs: &Self,
        from_other: bool,
    ) -> &mut Self {
        self.sub_inplace(rhs, from_other);
        self
    }

    /// \\( self = self - rhs \\) and `rhs` may be unchanged or equal to
    /// `self`, depending if `self.capacity >= rhs.capacity` or not.
    pub(crate) fn sub_mut_swap(&mut self, rhs: &mut Arbi) -> &mut Arbi {
        if rhs.capacity() > self.capacity() {
            // -(rhs - self) = self - rhs
            core::mem::swap(self, rhs);
            self.sub_mut(rhs);
            self.negate_mut();
        } else {
            self.sub_mut(rhs);
        }
        self
    }

    /// Return \\( self - rhs \\).
    pub(crate) fn sub_ref(&self, rhs: &Self) -> Arbi {
        // Ensure only one allocation.
        if rhs.size() > self.size() {
            // -(rhs - self) = self - rhs
            let mut ret = Arbi::with_capacity_and_copy(rhs.size(), rhs);
            ret.sub_mut(self);
            ret.negate_mut();
            ret
        } else {
            let mut ret = Arbi::with_capacity_and_copy(self.size(), self);
            ret.sub_mut(rhs);
            ret
        }
    }

    /// Return \\( |self| - |rhs| \\).
    pub(crate) fn sub_abs(mut self, mut rhs: Arbi) -> Arbi {
        if rhs.capacity() > self.capacity() {
            // |self| - |rhs| = -(|rhs| - |self|).
            rhs.sub_abs_mut(&self);
            rhs.negate_mut();
            rhs
        } else {
            self.sub_abs_mut(&rhs);
            self
        }
    }

    /// \\( self = |self| - |rhs| \\).
    pub(crate) fn sub_abs_mut(&mut self, rhs: &Self) -> &mut Self {
        self.sub_abs_mut_(rhs, false)
    }

    /// - \\( self = |rhs| - |self| \\) if `from_other` is `true`.
    /// - \\( self = |self| - |rhs| \\) if `from_other` is `false`.
    pub(crate) fn sub_abs_mut_(
        &mut self,
        rhs: &Self,
        from_other: bool,
    ) -> &mut Self {
        self.sub_abs_inplace(rhs, from_other);
        self
    }

    /// \\( self = |self| - |rhs| \\) and `rhs` may be unchanged or equal to
    /// `self`, depending if `self.capacity >= rhs.capacity` or not.
    pub(crate) fn sub_abs_mut_swap(&mut self, rhs: &mut Arbi) -> &mut Arbi {
        if rhs.capacity() > self.capacity() {
            // -(|rhs| - |self|) = |self| - |rhs|
            core::mem::swap(self, rhs);
            self.sub_abs_mut(rhs);
            self.negate_mut();
        } else {
            self.sub_abs_mut(rhs);
        }
        self
    }

    /// Return \\( |self| - |rhs| \\).
    pub(crate) fn sub_abs_ref(&self, rhs: &Self) -> Arbi {
        // Ensure only one allocation.
        if rhs.size() > self.size() {
            // |self| - |rhs| = -(|rhs| - |self|)
            let mut ret = Arbi::with_capacity_and_copy(rhs.size(), rhs);
            ret.sub_abs_mut(rhs);
            ret.negate_mut();
            ret
        } else {
            let mut ret = Arbi::with_capacity_and_copy(self.size(), self);
            ret.sub_abs_mut(rhs);
            ret
        }
    }
}
