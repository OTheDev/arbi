/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::macros::for_all_ints;
use crate::util::IntoArbiLikeArray;
use crate::Arbi;
use core::ops::{Add, AddAssign, Sub, SubAssign};

/* !impl_bit_with_int */
macro_rules! impl_add_with_int {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= i */

impl AddAssign<$int> for Arbi {
    fn add_assign(&mut self, rhs: $int) {
        let rhs = rhs.into_arbi_like_array();
        self.iadd_with_arbi_like_view((&rhs).into());
    }
}

impl SubAssign<$int> for Arbi {
    fn sub_assign(&mut self, rhs: $int) {
        let rhs = rhs.into_arbi_like_array();
        self.isub_with_arbi_like_view((&rhs).into());
    }
}

/* (2) a ⊕ i => a' */

impl Add<$int> for Arbi {
    type Output = Arbi;
    fn add(mut self, rhs: $int) -> Arbi {
        self += rhs;
        self
    }
}

impl Sub<$int> for Arbi {
    type Output = Arbi;
    fn sub(mut self, rhs: $int) -> Arbi {
        self -= rhs;
        self
    }
}

/* (3) i ⊕ a => a' */

impl Add<Arbi> for $int {
    type Output = Arbi;
    fn add(self, rhs: Arbi) -> Arbi {
        rhs + self
    }
}

impl Sub<Arbi> for $int {
    type Output = Arbi;
    fn sub(self, rhs: Arbi) -> Arbi {
        -(rhs - self)
    }
}

/* (4) &a ⊕ i => a' */

impl Add<$int> for &Arbi {
    type Output = Arbi;
    fn add(self, rhs: $int) -> Arbi {
        self.clone() + rhs
    }
}

impl Sub<$int> for &Arbi {
    type Output = Arbi;
    fn sub(self, rhs: $int) -> Arbi {
        self.clone() - rhs
    }
}

/* (5) i ⊕ &a => a' */

impl Add<&Arbi> for $int {
    type Output = Arbi;
    fn add(self, rhs: &Arbi) -> Arbi {
        rhs + self
    }
}

impl Sub<&Arbi> for $int {
    type Output = Arbi;
    fn sub(self, rhs: &Arbi) -> Arbi {
        -(rhs - self)
    }
}

        )*
    };
}
/* impl_bit_with_int! */

for_all_ints!(impl_add_with_int);

// Implements the same combinations as impl_add_with_int but with &i instead of
// i, using the above implementations.
macro_rules! impl_add_with_int_ref {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= &i */

impl AddAssign<&$int> for Arbi {
    fn add_assign(&mut self, rhs: &$int) {
        (*self) += (*rhs);
    }
}

impl SubAssign<&$int> for Arbi {
    fn sub_assign(&mut self, rhs: &$int) {
        (*self) -= (*rhs);
    }
}

/* (2) a ⊕ &i => a' */

impl Add<&$int> for Arbi {
    type Output = Arbi;
    fn add(self, rhs: &$int) -> Arbi {
        self + (*rhs)
    }
}

impl Sub<&$int> for Arbi {
    type Output = Arbi;
    fn sub(self, rhs: &$int) -> Arbi {
        self - (*rhs)
    }
}

/* (3) &i ⊕ a => a' */

impl Add<Arbi> for &$int {
    type Output = Arbi;
    fn add(self, rhs: Arbi) -> Arbi {
        (*self) + rhs
    }
}

impl Sub<Arbi> for &$int {
    type Output = Arbi;
    fn sub(self, rhs: Arbi) -> Arbi {
        (*self) - rhs
    }
}

/* (4) &a ⊕ &i => a' */

impl Add<&$int> for &Arbi {
    type Output = Arbi;
    fn add(self, rhs: &$int) -> Arbi {
        self + (*rhs)
    }
}

impl Sub<&$int> for &Arbi {
    type Output = Arbi;
    fn sub(self, rhs: &$int) -> Arbi {
        self - (*rhs)
    }
}

/* (5) &i ⊕ &a => a' */

impl Add<&Arbi> for &$int {
    type Output = Arbi;
    fn add(self, rhs: &Arbi) -> Arbi {
        (*self) + rhs
    }
}

impl Sub<&Arbi> for &$int {
    type Output = Arbi;
    fn sub(self, rhs: &Arbi) -> Arbi {
        (*self) - rhs
    }
}

        )*
    };
}
/* impl_bit_with_int_ref! */

for_all_ints!(impl_add_with_int_ref);
