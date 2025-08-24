/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::macros::for_all_ints;
use crate::util::IntoArbiLikeArray;
use crate::Arbi;
use core::ops::{Mul, MulAssign};

/* !impl_mul_with_int */
macro_rules! impl_mul_with_int {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= i */

impl MulAssign<$int> for Arbi {
    fn mul_assign(&mut self, rhs: $int) {
        let mut ret = Arbi::zero();
        let rhs = rhs.into_arbi_like_array();
        Self::mul_with_arbi_like_view(&mut ret, (&*self).into(), (&rhs).into());
        *self = core::mem::take(&mut ret);
    }
}

/* (2) a ⊕ i => a' */

impl Mul<$int> for Arbi {
    type Output = Self;
    fn mul(mut self, rhs: $int) -> Self {
        self *= rhs;
        self
    }
}

/* (3) i ⊕ a => a' */

impl Mul<Arbi> for $int {
    type Output = Arbi;
    fn mul(self, rhs: Arbi) -> Arbi {
        rhs * self
    }
}


/* (4) &a ⊕ i => a' */

impl Mul<$int> for &Arbi {
    type Output = Arbi;
    fn mul(self, rhs: $int) -> Arbi {
        self.clone() * rhs
    }
}

/* (5) i ⊕ &a => a' */

impl Mul<&Arbi> for $int {
    type Output = Arbi;
    fn mul(self, rhs: &Arbi) -> Arbi {
        rhs * self
    }
}

        )*
    }
}
/* impl_mul_with_int! */

for_all_ints!(impl_mul_with_int);

/* !impl_mul_with_int_ref */
macro_rules! impl_mul_with_int_ref {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= &i */

impl MulAssign<&$int> for Arbi {
    fn mul_assign(&mut self, rhs: &$int) {
        (*self) *= (*rhs);
    }
}

/* (2) a ⊕ &i => a' */

impl Mul<&$int> for Arbi {
    type Output = Self;
    fn mul(self, rhs: &$int) -> Self {
        self * (*rhs)
    }
}

/* (3) &i ⊕ a => a' */

impl Mul<Arbi> for &$int {
    type Output = Arbi;
    fn mul(self, rhs: Arbi) -> Arbi {
        (*self) * rhs
    }
}

/* (4) &a ⊕ &i => a' */

impl Mul<&$int> for &Arbi {
    type Output = Arbi;
    fn mul(self, rhs: &$int) -> Arbi {
        self * (*rhs)
    }
}

/* (5) &i ⊕ &a => a' */

impl Mul<&Arbi> for &$int {
    type Output = Arbi;
    fn mul(self, rhs: &Arbi) -> Arbi {
        (*self) * rhs
    }
}

        )*
    };
}
/* impl_mul_with_int_ref! */

for_all_ints!(impl_mul_with_int_ref);
