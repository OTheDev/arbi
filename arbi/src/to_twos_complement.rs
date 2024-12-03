/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

pub(crate) enum ByteOrder {
    Be,
    Le,
}

/// Perform two's complement on a slice of unsigned integers in-place.
pub(crate) trait TwosComplement {
    fn to_twos_complement(&mut self, order: ByteOrder);
}

/* !impl_twos_complement */
macro_rules! impl_twos_complement {
    ($($t:ty),*) => {
        $(

impl TwosComplement for [$t] {
    fn to_twos_complement(&mut self, order: ByteOrder) {
        let size: usize = self.len();
        let mut carry: bool = true;

        match order {
            ByteOrder::Le => {
                for item in self.iter_mut().take(size) {
                    let sum: $t =
                        (!(*item)).wrapping_add(if carry { 1 } else { 0 });
                    carry = sum < (carry as $t);
                    *item = sum;
                }
            }
            ByteOrder::Be => {
                for item in self.iter_mut().rev().take(size) {
                    let sum: $t =
                        (!(*item)).wrapping_add(if carry { 1 } else { 0 });
                    carry = sum < (carry as $t);
                    *item = sum;
                }
            }
        }
    }
}

        )*
    }
}
/* impl_twos_complement! */

impl_twos_complement!(u8, u16, u32, u64, u128, usize);
