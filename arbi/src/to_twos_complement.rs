/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};
use alloc::vec;
use alloc::vec::Vec;

impl Arbi {
    pub(crate) fn to_twos_complement(vec: &[Digit]) -> Vec<Digit> {
        let vec_size: usize = vec.len();
        let mut result: Vec<Digit> = vec![0; vec_size];
        let mut carry: bool = true;

        for i in 0..vec_size {
            let sum: Digit = (!vec[i]).wrapping_add(if carry { 1 } else { 0 });
            carry = sum < (carry as Digit);
            result[i] = sum;
        }

        result
    }

    pub(crate) fn to_twos_complement_inplace(vec: &mut [Digit]) {
        let vec_size: usize = vec.len();
        let mut carry: bool = true;

        for item in vec.iter_mut().take(vec_size) {
            let sum: Digit = (!(*item)).wrapping_add(if carry { 1 } else { 0 });
            carry = sum < (carry as Digit);
            *item = sum;
        }
    }
}
