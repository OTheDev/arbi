/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::{Arbi, Digit};
use core::ops::{Add, AddAssign, Sub, SubAssign};

impl Arbi {
    /// \\( |x| + |y| \\)
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

    /// \\( x + y \\)
    fn add_inplace(&mut self, y: &Self) {
        if self.negative() {
            if y.negative() {
                // x < 0, y < 0 ==> x = -|x|, y = -|y|. ==> x + y = -(|x| + |y|)
                self.add_abs_inplace(y);
                self.neg = true;
            } else {
                // x < 0, y >= 0 ==> x = -|x|, y = |y| ==> x + y = |y| - |x|
                self.sub_abs_inplace(y, true);
            }
        } else if y.negative() {
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
        self.neg = false;
    }

    /// |self| - |y|, assuming |self| > |y|.
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

    fn sub_inplace(&mut self, y: &Self) {
        if self.negative() {
            if y.negative() {
                // x < 0, y < 0 ==> x = -|x|, y = -|y| ==> x - y = |y| - |x|
                self.sub_abs_inplace(y, true);
            } else {
                // x < 0, y >= 0 ==> x = -|x|, y = |y| ==> x - y = -(|x| + |y|)
                self.add_abs_inplace(y);
                self.neg = true;
            }
        } else if y.negative() {
            // x >= 0, y < 0 ==> x = |x|, y = -|y| ==> x - y = |x| + |y|
            self.add_abs_inplace(y);
        } else {
            // x >= 0, y >= 0 ==> x = |x|, y = |y| ==> x - y = |x| - |y|
            self.sub_abs_inplace(y, false);
        }
    }

    /// \\( |x| - |y| \\)
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

                    if !from_other {
                        self.neg = true;
                    }
                } else {
                    self.sub_abs_gt_inplace(y);

                    if from_other {
                        self.neg = true;
                    }
                }
            }
            core::cmp::Ordering::Greater => {
                self.sub_abs_gt_inplace(y);

                if from_other {
                    self.neg = true;
                }
            }
            core::cmp::Ordering::Less => {
                self.resize_and_sub_abs_from_larger(y);

                if !from_other {
                    self.neg = true;
                }
            }
        }
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl Add<Arbi> for Arbi {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        self.add_inplace(&other);
        self
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'a> Add<&'a Arbi> for Arbi {
    type Output = Self;

    fn add(mut self, other: &'a Arbi) -> Self {
        self.add_inplace(other);
        self
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'b> Add<&'b Arbi> for &Arbi {
    type Output = Arbi;

    fn add(self, other: &'b Arbi) -> Arbi {
        let mut ret = self.clone();
        ret.add_inplace(other);
        ret
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl AddAssign for Arbi {
    fn add_assign(&mut self, other: Self) {
        self.add_inplace(&other);
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'a> AddAssign<&'a Arbi> for Arbi {
    fn add_assign(&mut self, other: &'a Arbi) {
        self.add_inplace(other);
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl Sub<Arbi> for Arbi {
    type Output = Self;

    fn sub(mut self, other: Self) -> Self {
        self.sub_inplace(&other);
        self
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'a> Sub<&'a Arbi> for Arbi {
    type Output = Self;

    fn sub(mut self, other: &'a Arbi) -> Self {
        self.sub_inplace(other);
        self
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'b> Sub<&'b Arbi> for &Arbi {
    type Output = Arbi;

    fn sub(self, other: &'b Arbi) -> Arbi {
        let mut ret = self.clone();
        ret.sub_inplace(other);
        ret
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl SubAssign for Arbi {
    fn sub_assign(&mut self, other: Self) {
        self.sub_inplace(&other);
    }
}

/// ## Complexity
/// \\( O(n) \\)
impl<'a> SubAssign<&'a Arbi> for Arbi {
    fn sub_assign(&mut self, other: &'a Arbi) {
        self.sub_inplace(other);
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
        let z = Arbi::from(0);

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
