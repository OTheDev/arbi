/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Digit;

#[allow(dead_code)]
pub(crate) fn s_shr(r: &mut [Digit], a: &[Digit], shift: u32) -> Digit {
    debug_assert!(shift > 0 && shift < Digit::BITS);
    debug_assert!(r.len() >= a.len());
    debug_assert!(!a.is_empty());

    let compl = Digit::BITS - shift;
    let res = a[0].wrapping_shl(compl);
    let mut lo = a[0].wrapping_shr(shift);
    for i in 1..a.len() {
        let hi = a[i];
        r[i - 1] = lo | hi.wrapping_shl(compl);
        lo = hi.wrapping_shr(shift);
    }
    r[a.len() - 1] = lo;
    res
}

pub(crate) fn s_ishr(a: &mut [Digit], shift: u32) -> Digit {
    debug_assert!(shift > 0 && shift < Digit::BITS);
    debug_assert!(!a.is_empty());

    let compl = Digit::BITS - shift;
    let res = a[0].wrapping_shl(compl);
    let mut lo = a[0].wrapping_shr(shift);
    for i in 1..a.len() {
        let hi = a[i];
        a[i - 1] = lo | hi.wrapping_shl(compl);
        lo = hi.wrapping_shr(shift);
    }
    a[a.len() - 1] = lo;
    res
}
