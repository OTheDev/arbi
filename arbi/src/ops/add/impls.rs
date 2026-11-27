/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::comparisons::s_cmp_normalized;
use crate::util::ArbiLikeView;
use crate::Arbi;
use crate::Digit;
use core::cmp::Ordering;

/* Low-Level Addition Routines */

fn uaddc(r: &mut Digit, a: Digit, b: Digit, carry: &mut bool) {
    let tmp = a.wrapping_add(*carry as Digit);
    *r = b.wrapping_add(tmp);
    *carry = *r < b || tmp < a;
}

/// a[0:n] += 1, true if overflow
pub(crate) fn s_inc(a: &mut [Digit]) -> bool {
    for digit in a {
        let tmp = digit.wrapping_add(1);
        if tmp >= *digit {
            // No overflow
            *digit = tmp;
            return false;
        }
        *digit = tmp;
    }
    true
}

/// a[0:n] += b, true if overflow
pub(crate) fn s_iadd_digit(a: &mut [Digit], b: Digit) -> bool {
    let (first, rest) = match a.split_first_mut() {
        Some(s) => s,
        None => return false,
    };
    let tmp = first.wrapping_add(b);
    let overflow = tmp < *first;
    *first = tmp;
    if overflow {
        s_inc(rest)
    } else {
        false
    }
}

/// a[0:n] += b[0:n], n the length of both slices, true if overflow
pub(crate) fn s_iadd_aligned(a: &mut [Digit], b: &[Digit]) -> bool {
    debug_assert_eq!(a.len(), b.len());
    let mut carry = false;
    let mut tmp: Digit = 0;
    for (a_digit, b_digit) in a.iter_mut().zip(b.iter()) {
        uaddc(&mut tmp, *a_digit, *b_digit, &mut carry);
        *a_digit = tmp;
    }
    carry
}

/// Assuming m >= n, a[0:m] += b[0:n], true if overflow
pub(crate) fn s_iadd(a: &mut [Digit], b: &[Digit]) -> bool {
    assert!(a.len() >= b.len());
    if s_iadd_aligned(&mut a[..b.len()], b) {
        s_inc(&mut a[b.len()..])
    } else {
        false
    }
}

/// r[0:n] = a[0:n] + b, returns carry
pub(crate) fn s_add_digit(r: &mut [Digit], a: &[Digit], b: Digit) -> bool {
    debug_assert_eq!(r.len(), a.len());
    debug_assert!(!a.is_empty());
    let mut carry = b;
    for (r_digit, &a_digit) in r.iter_mut().zip(a.iter()) {
        let sum = a_digit.wrapping_add(carry);
        carry = (sum < carry) as Digit;
        *r_digit = sum;
    }
    carry != 0
}

/// r[0:n] = a[0:n] + b[0:n], returns carry
pub(crate) fn s_add_aligned(r: &mut [Digit], a: &[Digit], b: &[Digit]) -> bool {
    debug_assert_eq!(r.len(), a.len());
    debug_assert_eq!(r.len(), b.len());
    let mut carry = 0;
    for ((r_digit, &a_digit), &b_digit) in
        r.iter_mut().zip(a.iter()).zip(b.iter())
    {
        let tmp = a_digit.wrapping_add(carry);
        carry = (tmp < carry) as Digit;
        let sum = tmp.wrapping_add(b_digit);
        carry += (sum < b_digit) as Digit;
        *r_digit = sum;
    }
    carry != 0
}

/// r[0:m] = a[0:m] + b[0:n], assumes m >= n, returns carry
#[allow(dead_code)]
pub(crate) fn s_add(r: &mut [Digit], a: &[Digit], b: &[Digit]) -> bool {
    debug_assert!(a.len() >= b.len());
    debug_assert_eq!(r.len(), a.len());
    let carry = s_add_aligned(&mut r[..b.len()], &a[..b.len()], b);
    if a.len() > b.len() {
        s_add_digit(&mut r[b.len()..], &a[b.len()..], carry as Digit)
    } else {
        carry
    }
}

/// r[0:n] = a[0:n] + b[0:n] + carry_in, returns carry_out
#[allow(dead_code)]
pub(crate) fn s_add_aligned_carry(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    carry_in: Digit,
) -> Digit {
    debug_assert_eq!(r.len(), a.len());
    debug_assert_eq!(r.len(), b.len());
    debug_assert!(carry_in <= 1, "carry_in must be 0 or 1");
    let mut carry = s_add_aligned(r, a, b) as Digit;
    carry += s_iadd_digit(r, carry_in) as Digit;
    carry
}

/* Low-Level Subtraction Routines */

fn usubb(r: &mut Digit, a: Digit, b: Digit, borrow: &mut bool) {
    let tmp = a.wrapping_sub(b);
    *r = tmp.wrapping_sub(*borrow as Digit);
    *borrow = *r > tmp || tmp > a;
}

/// a[0:n] -= 1, true if borrow
pub(crate) fn s_dec(a: &mut [Digit]) -> bool {
    for digit in a {
        let tmp = digit.wrapping_sub(1);
        if *digit != 0 {
            // No borrow
            *digit = tmp;
            return false;
        }
        *digit = tmp;
    }
    true
}

/// a[0:n] -= b, true if borrow
pub(crate) fn s_isub_digit(a: &mut [Digit], b: Digit) -> bool {
    let (first, rest) = match a.split_first_mut() {
        Some(s) => s,
        None => return false,
    };
    let tmp = first.wrapping_sub(b);
    let borrow = *first < b;
    *first = tmp;
    if borrow {
        s_dec(rest)
    } else {
        false
    }
}

/// a[0:n] -= b[0:n], n the length of both slices, true if borrow
pub(crate) fn s_isub_aligned(a: &mut [Digit], b: &[Digit]) -> bool {
    debug_assert_eq!(a.len(), b.len());
    let mut borrow = false;
    let mut tmp: Digit = 0;
    for (a_digit, b_digit) in a.iter_mut().zip(b.iter()) {
        usubb(&mut tmp, *a_digit, *b_digit, &mut borrow);
        *a_digit = tmp;
    }
    borrow
}

/// a[0:n] = b[0:n] - a[0:n], n the length of both slices, true if borrow
pub(crate) fn s_isub_aligned_from_other(a: &mut [Digit], b: &[Digit]) -> bool {
    debug_assert_eq!(a.len(), b.len());
    let mut borrow = false;
    let mut tmp: Digit = 0;
    for (a_digit, b_digit) in a.iter_mut().zip(b.iter()) {
        usubb(&mut tmp, *b_digit, *a_digit, &mut borrow);
        *a_digit = tmp;
    }
    borrow
}

// TODO: rename.
/// Assuming m >= n, a[0:m] -= b[0:n], true if borrow (which implies b > a)
pub(crate) fn s_isub(a: &mut [Digit], b: &[Digit]) -> bool {
    assert!(a.len() >= b.len());
    if s_isub_aligned(&mut a[..b.len()], b) {
        s_dec(&mut a[b.len()..])
    } else {
        false
    }
}

// r[0:n] = a[0:n] - b, returns borrow
pub(crate) fn s_sub_digit(r: &mut [Digit], a: &[Digit], b: Digit) -> bool {
    debug_assert_eq!(r.len(), a.len());
    debug_assert!(!a.is_empty());
    let mut borrow = b;
    for (r_digit, &a_digit) in r.iter_mut().zip(a.iter()) {
        let cy = (a_digit < borrow) as Digit;
        *r_digit = a_digit.wrapping_sub(borrow);
        borrow = cy;
    }
    borrow != 0
}

/// r[0:n] = a[0:n] - b[0:n], returns borrow
pub(crate) fn s_sub_aligned(r: &mut [Digit], a: &[Digit], b: &[Digit]) -> bool {
    debug_assert_eq!(r.len(), a.len());
    debug_assert_eq!(r.len(), b.len());
    let mut borrow = 0;
    for ((r_digit, &a_digit), &b_digit) in
        r.iter_mut().zip(a.iter()).zip(b.iter())
    {
        let tmp = b_digit.wrapping_add(borrow);
        borrow = (tmp < borrow) as Digit;
        borrow += (a_digit < tmp) as Digit;
        *r_digit = a_digit.wrapping_sub(tmp);
    }
    borrow != 0
}

/// r[0:m] = a[0:m] - b[0:n], assumes m >= n, returns borrow
pub(crate) fn s_sub(r: &mut [Digit], a: &[Digit], b: &[Digit]) -> bool {
    debug_assert!(a.len() >= b.len());
    debug_assert_eq!(r.len(), a.len());
    let borrow = s_sub_aligned(&mut r[..b.len()], &a[..b.len()], b);
    if a.len() > b.len() {
        s_sub_digit(&mut r[b.len()..], &a[b.len()..], borrow as Digit)
    } else {
        borrow
    }
}

/// r[0:n] = a[0:n] - b[0:n] - borrow_in, returns borrow_out
#[allow(dead_code)]
pub(crate) fn s_sub_aligned_borrow(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    borrow_in: Digit,
) -> Digit {
    debug_assert_eq!(r.len(), a.len());
    debug_assert_eq!(r.len(), b.len());
    debug_assert!(borrow_in <= 1, "borrow_in must be 0 or 1");
    let mut borrow = s_sub_aligned(r, a, b) as Digit;
    borrow += s_isub_digit(r, borrow_in) as Digit;
    borrow
}

impl Arbi {
    /// |self| = |self| + |b|
    pub(crate) fn iadd_mag(&mut self, b: &[Digit]) {
        // We only allocate when necessary.
        if self.vec.len() >= b.len() {
            if s_iadd(&mut self.vec, b) {
                self.vec.push(1);
            }
        } else {
            let size = self.vec.len();
            let carry = s_iadd_aligned(&mut self.vec, &b[..size]);
            self.vec.extend_from_slice(&b[size..]);
            if carry && s_inc(&mut self.vec[size..]) {
                self.vec.push(1);
            }
        }
        self.trim();
    }

    /// |self| = |self| - |b|, assuming |b| <= |self|
    pub(crate) fn isub_mag(&mut self, b: &[Digit]) {
        assert!(!s_isub(&mut self.vec, b));
        self.trim();
    }

    /// |self| = |b| - |self|, assuming |b| >= |self|
    pub(crate) fn isub_mag_from_other(&mut self, b: &[Digit]) {
        assert!(b.len() >= self.vec.len());
        let size = self.vec.len();
        let borrow = s_isub_aligned_from_other(&mut self.vec, &b[..size]);
        self.vec.extend_from_slice(&b[size..]);
        if borrow {
            assert!(!s_dec(&mut self.vec[size..]));
        }
        self.trim();
    }
}

/* Higher-Level Signed Addition/Subtraction */

impl Arbi {
    /// self += other
    pub(crate) fn iadd(&mut self, other: &Arbi) {
        if self.neg == other.neg {
            // Case 1) a, b < 0 ==> a + b = (-|a|) + (-|b|) = -(|a| + |b|)
            // Case 2) a, b >= 0 ==> a + b = |a| + |b|
            // Same signs: add magnitudes
            self.iadd_mag(&other.vec);
        } else {
            match s_cmp_normalized(&self.vec, &other.vec) {
                Ordering::Greater => {
                    // |a| > |b|
                    // a < 0, b >= 0 ==> a + b = -|a| + |b| = -(|a| - |b|) < 0, keep sign of a
                    // a >= 0, b < 0 ==> a + b = |a| - |b| > 0, keep sign of a
                    self.isub_mag(&other.vec);
                }
                Ordering::Less => {
                    // |a| < |b|
                    // a < 0, b >= 0 ==> a + b = |b| - |a| > 0, use b's sign
                    // a >= 0, b < 0 ==> a + b = -(|b| - |a|) < 0, use b's sign
                    self.isub_mag_from_other(&other.vec);
                    self.neg = other.neg;
                }
                Ordering::Equal => {
                    // |a| = |b|
                    self.make_zero();
                }
            }
        }
    }

    /// self -= other
    pub(crate) fn isub(&mut self, other: &Arbi) {
        if self.neg != other.neg {
            // a < 0, b >= 0 ==> a - b = -|a| - |b| = -(|a| + |b|), keep sign of a
            // a >= 0, b < 0 ==> a - b = |a| - (-|b|) = |a| + |b|, keep sign of a
            self.iadd_mag(&other.vec);
        } else {
            match s_cmp_normalized(&self.vec, &other.vec) {
                Ordering::Greater => {
                    // |a| > |b|
                    // a, b < 0 ==> a - b = -|a| - (-|b|) = |b| - |a| < 0, keep sign
                    // a, b >= 0 ==> a - b = |a| - |b| >= 0, keep sign
                    self.isub_mag(&other.vec);
                }
                Ordering::Less => {
                    // |a| < |b|
                    // a, b < 0 ==> a - b = |b| - |a| > 0, flip sign
                    // a, b >= 0 ==> a - b = -(|b| - |a|) < 0, flip sign
                    self.isub_mag_from_other(&other.vec);
                    self.neg = !self.neg;
                }
                Ordering::Equal => {
                    // |a| = |b|
                    // a, b < 0 ==> a - b = -|a| - (-|b|) = |b| - |a| = 0
                    // a, b >= 0 ==> a - b = |a| - |b| = 0
                    self.make_zero();
                }
            }
        }
    }

    pub(crate) fn iadd_with_arbi_like_view(&mut self, other: ArbiLikeView) {
        if self.neg == other.neg {
            // Case 1) a, b < 0 ==> a + b = (-|a|) + (-|b|) = -(|a| + |b|)
            // Case 2) a, b >= 0 ==> a + b = |a| + |b|
            // Same signs: add magnitudes
            self.iadd_mag(other.vec);
        } else {
            match s_cmp_normalized(&self.vec, other.vec) {
                Ordering::Greater => {
                    // |a| > |b|
                    // a < 0, b >= 0 ==> a + b = -|a| + |b| = -(|a| - |b|) < 0, keep sign of a
                    // a >= 0, b < 0 ==> a + b = |a| - |b| > 0, keep sign of a
                    self.isub_mag(other.vec);
                }
                Ordering::Less => {
                    // |a| < |b|
                    // a < 0, b >= 0 ==> a + b = |b| - |a| > 0, use b's sign
                    // a >= 0, b < 0 ==> a + b = -(|b| - |a|) < 0, use b's sign
                    self.isub_mag_from_other(other.vec);
                    self.neg = other.neg;
                }
                Ordering::Equal => {
                    // |a| = |b|
                    self.make_zero();
                }
            }
        }
    }

    pub(crate) fn isub_with_arbi_like_view(&mut self, other: ArbiLikeView) {
        if self.neg != other.neg {
            // a < 0, b >= 0 ==> a - b = -|a| - |b| = -(|a| + |b|), keep sign of a
            // a >= 0, b < 0 ==> a - b = |a| - (-|b|) = |a| + |b|, keep sign of a
            self.iadd_mag(other.vec);
        } else {
            match s_cmp_normalized(&self.vec, other.vec) {
                Ordering::Greater => {
                    // |a| > |b|
                    // a, b < 0 ==> a - b = -|a| - (-|b|) = |b| - |a| < 0, keep sign
                    // a, b >= 0 ==> a - b = |a| - |b| >= 0, keep sign
                    self.isub_mag(other.vec);
                }
                Ordering::Less => {
                    // |a| < |b|
                    // a, b < 0 ==> a - b = |b| - |a| > 0, flip sign
                    // a, b >= 0 ==> a - b = -(|b| - |a|) < 0, flip sign
                    self.isub_mag_from_other(other.vec);
                    self.neg = !self.neg;
                }
                Ordering::Equal => {
                    // |a| = |b|
                    // a, b < 0 ==> a - b = -|a| - (-|b|) = |b| - |a| = 0
                    // a, b >= 0 ==> a - b = |a| - |b| = 0
                    self.make_zero();
                }
            }
        }
    }
}
