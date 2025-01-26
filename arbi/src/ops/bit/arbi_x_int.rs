/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
Let ⊕ denote any one of &, |, ^. Let a denote an (owned) arbitary Arbi and i an
arbitrary primitive integer. Let a' denote the result (an Arbi). Here, "inplace"
means memory allocation need not occur if there's already enough capacity in a.

Implements:
    1. a ⊕= i           (inplace)
    2. a ⊕ i    => a'   (inplace)
    3. i ⊕ a    => a'   (inplace)
    4. &a ⊕ i   => a'   (clone)
    5. i ⊕ &a   => a'   (clone)

Moreover, there's already code implemented that can be used to assign the result
of (4) and (5) to an existing buffer, potentially avoiding memory allocation,
but first, an API needs to be decided for expressing such operations.

The same five combinations are also implemented with i replaced by &i, for
convenience.
*/

use crate::macros::for_all_ints;
use crate::ops::bit::impls::BitwiseOp;
use crate::util::IntoArbiLikeArray;
use crate::Arbi;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
};

/* !impl_bit_with_int */
macro_rules! impl_bit_with_int {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= i */
impl BitAndAssign<$int> for Arbi {
    fn bitand_assign(&mut self, rhs: $int) {
        let rhs = rhs.into_arbi_like_array();
        self.inplace_bitwise_op_with_arbi_like_view((&rhs).into(), BitwiseOp::And);
    }
}

impl BitOrAssign<$int> for Arbi {
    fn bitor_assign(&mut self, rhs: $int) {
        let rhs = rhs.into_arbi_like_array();
        self.inplace_bitwise_op_with_arbi_like_view((&rhs).into(), BitwiseOp::Ior);
    }
}

impl BitXorAssign<$int> for Arbi {
    fn bitxor_assign(&mut self, rhs: $int) {
        let rhs = rhs.into_arbi_like_array();
        self.inplace_bitwise_op_with_arbi_like_view((&rhs).into(), BitwiseOp::Xor);
    }
}

/* (2) a ⊕ i => a' */
impl BitAnd<$int> for Arbi {
    type Output = Arbi;
    fn bitand(mut self, rhs: $int) -> Arbi {
        self &= rhs;
        self
    }
}

impl BitOr<$int> for Arbi {
    type Output = Arbi;
    fn bitor(mut self, rhs: $int) -> Arbi {
        self |= rhs;
        self
    }
}

impl BitXor<$int> for Arbi {
    type Output = Arbi;
    fn bitxor(mut self, rhs: $int) -> Arbi {
        self ^= rhs;
        self
    }
}

/* (3) i ⊕ a => a' */
impl BitAnd<Arbi> for $int {
    type Output = Arbi;
    fn bitand(self, mut rhs: Arbi) -> Arbi {
        rhs &= self;
        rhs
    }
}

impl BitOr<Arbi> for $int {
    type Output = Arbi;
    fn bitor(self, mut rhs: Arbi) -> Arbi {
        rhs |= self;
        rhs
    }
}

impl BitXor<Arbi> for $int {
    type Output = Arbi;
    fn bitxor(self, mut rhs: Arbi) -> Arbi {
        rhs ^= self;
        rhs
    }
}

/* (4) &a ⊕ i => a' */
impl BitAnd<$int> for &Arbi {
    type Output = Arbi;
    fn bitand(self, rhs: $int) -> Arbi {
        self.clone() & rhs
    }
}

impl BitOr<$int> for &Arbi {
    type Output = Arbi;
    fn bitor(self, rhs: $int) -> Arbi {
        self.clone() | rhs
    }
}

impl BitXor<$int> for &Arbi {
    type Output = Arbi;
    fn bitxor(self, rhs: $int) -> Arbi {
        self.clone() ^ rhs
    }
}

/* (5) i ⊕ &a => a' */
impl BitAnd<&Arbi> for $int {
    type Output = Arbi;
    fn bitand(self, rhs: &Arbi) -> Arbi {
        rhs & self
    }
}

impl BitOr<&Arbi> for $int {
    type Output = Arbi;
    fn bitor(self, rhs: &Arbi) -> Arbi {
        rhs | self
    }
}

impl BitXor<&Arbi> for $int {
    type Output = Arbi;
    fn bitxor(self, rhs: &Arbi) -> Arbi {
        rhs ^ self
    }
}

        )*
    };
}
/* impl_bit_with_int! */

for_all_ints!(impl_bit_with_int);

// Implements the same combinations as impl_bit_with_int but with &i instead of
// i, using the above implementations.
//
// TODO: Can we use a macro to avoid doing this for every binop?
/* !impl_bit_with_int_ref */
macro_rules! impl_bit_with_int_ref {
    ($($int:ty),*) => {
        $(

/* (1) a ⊕= &i */
impl BitAndAssign<&$int> for Arbi {
    fn bitand_assign(&mut self, rhs: &$int) {
        (*self) &= (*rhs);
    }
}

impl BitOrAssign<&$int> for Arbi {
    fn bitor_assign(&mut self, rhs: &$int) {
        (*self) |= (*rhs);
    }
}

impl BitXorAssign<&$int> for Arbi {
    fn bitxor_assign(&mut self, rhs: &$int) {
        (*self) ^= (*rhs);
    }
}

/* (2) a ⊕ &i => a' */
impl BitAnd<&$int> for Arbi {
    type Output = Arbi;
    fn bitand(self, rhs: &$int) -> Arbi {
        self & (*rhs)
    }
}

impl BitOr<&$int> for Arbi {
    type Output = Arbi;
    fn bitor(self, rhs: &$int) -> Arbi {
        self | (*rhs)
    }
}

impl BitXor<&$int> for Arbi {
    type Output = Arbi;
    fn bitxor(self, rhs: &$int) -> Arbi {
        self ^ (*rhs)
    }
}

/* (3) &i ⊕ a => a' */
impl BitAnd<Arbi> for &$int {
    type Output = Arbi;
    fn bitand(self, rhs: Arbi) -> Arbi {
        (*self) & rhs
    }
}

impl BitOr<Arbi> for &$int {
    type Output = Arbi;
    fn bitor(self, rhs: Arbi) -> Arbi {
        (*self) | rhs
    }
}

impl BitXor<Arbi> for &$int {
    type Output = Arbi;
    fn bitxor(self, rhs: Arbi) -> Arbi {
        (*self) ^ rhs
    }
}

/* (4) &a ⊕ &i => a' */
impl BitAnd<&$int> for &Arbi {
    type Output = Arbi;
    fn bitand(self, rhs: &$int) -> Arbi {
        self & (*rhs)
    }
}

impl BitOr<&$int> for &Arbi {
    type Output = Arbi;
    fn bitor(self, rhs: &$int) -> Arbi {
        self | (*rhs)
    }
}

impl BitXor<&$int> for &Arbi {
    type Output = Arbi;
    fn bitxor(self, rhs: &$int) -> Arbi {
        self ^ (*rhs)
    }
}

/* (5) &i ⊕ &a => a' */
impl BitAnd<&Arbi> for &$int {
    type Output = Arbi;
    fn bitand(self, rhs: &Arbi) -> Arbi {
        (*self) & rhs
    }
}

impl BitOr<&Arbi> for &$int {
    type Output = Arbi;
    fn bitor(self, rhs: &Arbi) -> Arbi {
        (*self) | rhs
    }
}

impl BitXor<&Arbi> for &$int {
    type Output = Arbi;
    fn bitxor(self, rhs: &Arbi) -> Arbi {
        (*self) ^ rhs
    }
}

        )*
    };
}
/* impl_bit_with_int_ref! */

for_all_ints!(impl_bit_with_int_ref);
