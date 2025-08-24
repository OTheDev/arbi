/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use core::ops::{Mul, MulAssign};

/// `a *= &b`
impl<'a> MulAssign<&'a Arbi> for Arbi {
    fn mul_assign(&mut self, other: &'a Arbi) {
        self.mul_assign_(other);
    }
}

/// `a *= b`
impl MulAssign<Arbi> for Arbi {
    fn mul_assign(&mut self, mut other: Arbi) {
        if other.capacity() > self.capacity() {
            core::mem::swap(self, &mut other);
        }
        *self *= &other;
    }
}

/// `a * b`
impl Mul<Arbi> for Arbi {
    type Output = Self;
    fn mul(self, other: Self) -> Self::Output {
        let mut ret = Arbi::zero();
        Self::mul_(&mut ret, &self, &other);
        ret
        // self *= other;
        // self
    }
}

/// `a * &b`
impl<'a> Mul<&'a Arbi> for Arbi {
    type Output = Self;
    fn mul(self, other: &'a Arbi) -> Self {
        let mut ret = Arbi::zero();
        Self::mul_(&mut ret, &self, other);
        ret
        // self *= other;
        // self
    }
}

/// `&a * b`
impl Mul<Arbi> for &Arbi {
    type Output = Arbi;
    fn mul(self, other: Arbi) -> Arbi {
        let mut ret = Arbi::zero();
        Arbi::mul_(&mut ret, self, &other);
        ret
        // other *= self;
        // other
    }
}

/// `&a * &b`
impl<'b> Mul<&'b Arbi> for &Arbi {
    type Output = Arbi;
    fn mul(self, other: &'b Arbi) -> Self::Output {
        let mut ret = Arbi::zero();
        Arbi::mul_(&mut ret, self, other);
        ret
    }
}
