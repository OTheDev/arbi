/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::ops::add::impls::s_iadd_digit;
use crate::DDigit;
use crate::Digit;

#[allow(dead_code)]
pub(crate) fn s_shl(r: &mut [Digit], a: &[Digit], shift: u32) -> Digit {
    debug_assert!(shift > 0 && shift < Digit::BITS);
    debug_assert!(r.len() >= a.len());
    debug_assert!(!a.is_empty());

    let compl = Digit::BITS - shift;
    let mut lo = a[a.len() - 1];
    let res = lo.wrapping_shr(compl);
    let mut hi = lo.wrapping_shl(shift);
    for i in (1..a.len()).rev() {
        lo = a[i - 1];
        r[i] = hi | lo.wrapping_shr(compl);
        hi = lo.wrapping_shl(shift);
    }
    r[0] = hi;
    res
}

#[allow(dead_code)]
pub(crate) fn s_ishl(a: &mut [Digit], shift: u32) -> Digit {
    debug_assert!(shift > 0 && shift < Digit::BITS);
    debug_assert!(!a.is_empty());

    let compl = Digit::BITS - shift;
    let mut lo = a[a.len() - 1];
    let res = lo.wrapping_shr(compl);
    let mut hi = lo.wrapping_shl(shift);
    for i in (1..a.len()).rev() {
        lo = a[i - 1];
        a[i] = hi | lo.wrapping_shr(compl);
        hi = lo.wrapping_shl(shift);
    }
    a[0] = hi;
    res
}

/// r[0:m] += a[0:n] << shift, assuming m >= n
pub(crate) fn s_add_shl(r: &mut [Digit], a: &[Digit], shift: u32) -> Digit {
    debug_assert!(r.len() >= a.len());
    debug_assert!(shift > 0 && shift < Digit::BITS);
    debug_assert!(!a.is_empty());

    let mut carry: Digit = 0;
    let compl = Digit::BITS - shift;
    let mut hi = 0;
    for i in 0..a.len() {
        let lo = a[i];
        let shifted = hi | lo.wrapping_shl(shift);
        hi = lo.wrapping_shr(compl);
        let tmp = (r[i] as DDigit) + (shifted as DDigit) + (carry as DDigit);
        carry = (tmp >> Digit::BITS) as Digit;
        r[i] = tmp as Digit;
    }
    carry = carry.wrapping_add(hi);
    if carry != 0 {
        s_iadd_digit(&mut r[a.len()..], carry) as Digit
    } else {
        carry
    }
}
