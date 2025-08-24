/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{DDigit, Digit};

#[allow(dead_code)]
pub(crate) fn s_divrem_digit(q: &mut [Digit], u: &[Digit], v: Digit) -> Digit {
    let mut rem: DDigit = 0;
    for i in (0..u.len()).rev() {
        let temp = (rem << Digit::BITS) | u[i] as DDigit;
        q[i] = (temp / v as DDigit) as Digit;
        rem = temp % v as DDigit;
    }
    rem as Digit
}

#[allow(dead_code)]
pub(crate) fn s_idivrem_digit(q: &mut [Digit], v: Digit) -> Digit {
    let mut rem: DDigit = 0;
    for i in (0..q.len()).rev() {
        let temp = (rem << Digit::BITS) | q[i] as DDigit;
        q[i] = (temp / v as DDigit) as Digit;
        rem = temp % v as DDigit;
    }
    rem as Digit
}
