/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use super::square::s_square;
use crate::comparisons::s_cmp;
use crate::ops::add::impls::{
    s_iadd, s_iadd_digit, s_isub, s_isub_aligned_from_other, s_isub_digit,
    s_sub,
};
use crate::ops::div::impls::s_idivrem_digit;
use crate::ops::mul::{scratch_size, square_scratch_size};
use crate::ops::mul::{MUL_KARATSUBA_CUTOFF, MUL_TOOMCOOK3_CUTOFF};
use crate::ops::shl::impls::s_add_shl;
use crate::ops::shr::impls::s_ishr;
use crate::util::ArbiLikeView;
use crate::Arbi;
use crate::{DDigit, Digit};
use alloc::vec;
use core::cmp::Ordering;
use core::cmp::Ordering::{Equal, Greater, Less};

/* Low-Level Multiplication Routines */

/// r[0:n] += a[0:n] * b
#[inline]
pub(crate) fn s_add_muldigit_aligned(
    r: &mut [Digit],
    a: &[Digit],
    b: Digit,
) -> Digit {
    debug_assert_eq!(r.len(), a.len());
    let mut k: Digit = 0;
    for (rd, &ad) in r.iter_mut().zip(a) {
        let t =
            (*rd as DDigit) + (ad as DDigit) * (b as DDigit) + (k as DDigit);
        k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
        *rd = t as Digit; // t mod 2^{Digit::BITS}
    }
    k
}

/// r[0:m] += a[0:n] * b, assuming m >= n
#[inline]
pub(crate) fn s_add_muldigit(r: &mut [Digit], a: &[Digit], b: Digit) -> Digit {
    debug_assert!(r.len() >= a.len());
    let k = s_add_muldigit_aligned(&mut r[0..a.len()], a, b);
    if a.len() < r.len() {
        s_iadd_digit(&mut r[a.len()..], k) as Digit
    } else {
        k
    }
}

/// r[0:n] = r[0:n] * a + k
// TODO: replace imul1add1() usage with this.
#[inline]
#[allow(dead_code)]
pub(crate) fn s_imul_digit_add_digit(
    r: &mut [Digit],
    a: Digit,
    mut k: Digit,
) -> Digit {
    for d in r {
        let t = (*d as DDigit) * (a as DDigit) + (k as DDigit);
        k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
        *d = t as Digit; // t mod 2^{Digit::BITS}
    }
    k
}

/// r[0:n] = a[0:n] * b
#[inline]
pub(crate) fn s_mul_digit(r: &mut [Digit], a: &[Digit], b: Digit) -> Digit {
    debug_assert_eq!(r.len(), a.len());
    let mut k: Digit = 0;
    for (rd, &ad) in r.iter_mut().zip(a) {
        let t = (ad as DDigit) * (b as DDigit) + (k as DDigit);
        k = (t >> Digit::BITS) as Digit;
        *rd = t as Digit;
    }
    k
}

/// r[0:n] -= a[0:n] * b
#[inline]
pub(crate) fn s_sub_muldigit_aligned(
    r: &mut [Digit],
    a: &[Digit],
    b: Digit,
) -> Digit {
    debug_assert_eq!(r.len(), a.len());
    let mut k: Digit = 0;
    for (rd, &ad) in r.iter_mut().zip(a) {
        let tmp = (ad as DDigit) * (b as DDigit) + (k as DDigit);
        let hi = (tmp >> Digit::BITS) as Digit;
        let lo = tmp as Digit;
        let or = *rd;
        *rd = rd.wrapping_sub(lo);
        k = hi + (or < lo) as Digit;
    }
    k
}

/// r[0:m] -= a[0:n] * b, assuming m >= n
#[inline]
pub(crate) fn s_sub_muldigit(r: &mut [Digit], a: &[Digit], b: Digit) -> Digit {
    debug_assert!(r.len() >= a.len());
    let borrow = s_sub_muldigit_aligned(&mut r[0..a.len()], a, b);
    if a.len() < r.len() {
        s_isub_digit(&mut r[a.len()..], borrow) as Digit
    } else {
        borrow
    }
}

/* Grade School */

/// r[0:m+n] = a[0:m] * b[0:n], assuming m >= n >= 1
// Knuth Algorithm M essentially, but avoiding the zeroing step r[..m].fill(0).
pub(crate) fn s_mul_gradeschool(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
) -> Digit {
    debug_assert!(a.len() >= b.len());
    debug_assert!(!b.is_empty());
    debug_assert!(r.len() >= a.len() + b.len());
    r[a.len()] = s_mul_digit(&mut r[..a.len()], a, b[0]);
    for (j, &bd) in b.iter().enumerate().skip(1) {
        r[j + a.len()] = s_add_muldigit(&mut r[j..j + a.len()], a, bd);
    }
    r[a.len() + b.len() - 1]
}

/*
Karatsuba Multiplication O(n^1.585)
--------------------------------------------------------------------------------
Based on Brent and Zimmermann Algorithm 1.3 (KaratsubaMultiply)

    Input:
        a = a[0] + a[1]B^1 + a[2]B^2 + ... + a[n-1]B^(n-1)
        b = b[0] + b[1]B^1 + b[2]B^2 + ... + b[n-1]B^(n-1)

    Output:
        c = AB := c[0] + c[1]B^1 + ... + c[2n-1]B^(2n-1)

    Algorithm:
        k <- ceil(n/2)
        (a0, b0) := (a, b) mod B^k, (a1, b1) := (a, b) div B^k
        sa <- sign(a0 - a1), sb <- sign(b0 - b1)

        c0 <- a0 * b0
        c1 <- a1 * b1
        c2 <- |a0 - a1| * |b0 - b1|

        return c := c0 + (c0 + c1 - sa * sb * c2) * B^k + c1 * B^(2k).

Expressed in a Toom-Cook-type framework:

    (1) split a, b into a0, a1 and b0, b1

        a = a0 + a1 * t     (a0 has k "digits", a1 has (n-k) "digits")
        b = b0 + b1 * t

        k = ceil(n/2), t = B^k

    (2) Evaluation

        v0    = a0 * b0
        vinf  = a1 * b1
        vneg1 = |a0 - a1| * |b0 - b1|

        [sa := sign(a0 - a1), sb := sign(b0 - b1)]

    (3) Interpolation

        vmid = v0 + vinf - (sa * sb * vneg1)

        [note that sa * sb * vneg1 is effectively (a0 - a1) * (b0 - b1)]

    (4) Recomposition

        c = v0 + vmid * t + vinf * t^2
*/
/// r[0:2*n] = a[0:n] * b[0:n], assuming equal lengths
// TODO: This is already quite efficient, but it can be optimized.
pub(crate) fn s_mul_karatsuba_aligned(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    scratch: &mut [Digit],
) {
    debug_assert_eq!(a.len(), b.len());
    debug_assert!(r.len() >= 2 * a.len());

    /* (1) Split a, b into two parts: a0, a1 and b0, b1 */
    let n = a.len();
    let k = (n + 1) / 2; // ceil(n/2)
    let nr = n - k;

    let a0 = &a[0..k];
    let a1 = &a[k..];
    let b0 = &b[0..k];
    let b1 = &b[k..];

    /* (2) Evaluation
     * Result buffer is initially used to store |a0-a1| in r[0..k] and |b0-b1|
     * in r[k..2*k] for the vneg1 computation. After vneg1 is computed, v0 and
     * vinf are directly stored in r[0..2*k] and r[2*k..2*k+2*nr], respectively.
     */
    let mut sa = false;
    let mut sb = false;
    match s_cmp(a0, a1) {
        Greater => {
            s_sub(&mut r[0..k], a0, a1);
        }
        Less => {
            s_sub(&mut r[0..k], a1, a0);
            sa = true;
        }
        Equal => {
            r[0..k].fill(0);
        }
    }
    match s_cmp(b0, b1) {
        Greater => {
            s_sub(&mut r[k..2 * k], b0, b1);
        }
        Less => {
            s_sub(&mut r[k..2 * k], b1, b0);
            sb = true;
        }
        Equal => {
            r[k..2 * k].fill(0);
        }
    }

    // Zero only what we use directly, other multiplication routines do the same.
    scratch[..2 * k + 2].fill(0);
    let (vneg1_buf, recursive_scratch) = scratch.split_at_mut(2 * k + 2);

    // vneg1 = |a0 - a1| * |b0 - b1|
    s_mul_aligned(
        &mut vneg1_buf[..2 * k],
        &r[0..k],
        &r[k..2 * k],
        recursive_scratch,
    );
    // v0 = a0 * b0
    s_mul_aligned(&mut r[0..2 * k], a0, b0, recursive_scratch);
    // vinf  = a1 * b1
    s_mul_aligned(&mut r[2 * k..2 * k + 2 * nr], a1, b1, recursive_scratch);

    /* (3) Interpolation: vmid = v0 + vinf - (sa * sb * vneg1) */
    let vmid_buf = vneg1_buf;
    if sa ^ sb {
        s_iadd(vmid_buf, &r[0..2 * k]);
        s_iadd(vmid_buf, &r[2 * k..2 * k + 2 * nr]);
    } else {
        recursive_scratch[..2 * k].copy_from_slice(&vmid_buf[..2 * k]);
        vmid_buf[..2 * k].copy_from_slice(&r[0..2 * k]);
        s_iadd(vmid_buf, &r[2 * k..2 * k + 2 * nr]);
        s_isub(vmid_buf, &recursive_scratch[..2 * k]);
    }

    /* (4) Recomposition (v0, vinf already in r[0..2*k] and r[2*k..2*k+2*nr]) */
    s_iadd(&mut r[k..], vmid_buf);
}

/*
Toom-Cook 3-Way Multiplication O(n^1.465)
--------------------------------------------------------------------------------
Based on "Towards Optimal Toom-Cook Multiplication..." (Bodrato 2007, Appendix).

    U = U2*x^2 + U1*x + U0
    V = V2*x^2 + V1*x + V0

    Evaluation
    ----------------------------------------------------------------------------
        W0 = U2 + U0 ; W4 = V2 + V0
        W2 = W0 - U1 ; W1 = W4 - V1
        W0 = W0 + U1 ; W4 = W4 + V1
        W3 = W2 * W1 ; W1 = W0 * W4
        W0 =(W0 + U2)<<1-U0; W4 =(W4 + V2)<<1-V0
        W2 = W0 * W4
        W0 = U0 * V0 ; W4 = U2 * V2

            same as

        (1) W0 = U0 * V0
        (2) W1 = (U2 + U0 + U1) * (V2 + V0 + V1)
        (3) W2 = (U0 + 2U1 + 4U2) * (V0 + 2V1 + 4V2)
        (4) W3 = ((U2 + U0) - U1) * ((V2 + V0) - V1)
        (5) W4 = U2 * V2

    Interpolation
    ----------------------------------------------------------------------------
        W2 = (W2 - W3)/3
        W3 = (W1 - W3)>>1
        W1 = W1 - W0
        W2 = (W2 - W1)>>1 - W4<<1
        W1 = W1 - W3 - W4
        W3 = W3 - W2

    Recomposition
    ----------------------------------------------------------------------------
        W = W4*x^4+ W2*x^3+ W1*x^2+ W3*x + W0
        W == U*V
*/
/// r[0:2*n] = a[0:n] * b[0:n], assuming equal lengths
pub(crate) fn s_mul_toomcook3_aligned(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    scratch: &mut [Digit],
) {
    debug_assert_eq!(a.len(), b.len());
    debug_assert!(r.len() >= 2 * a.len());

    let n = a.len();
    let k = (n + 2) / 3;
    let nr = n - 2 * k;

    let a0 = &a[0..k];
    let a1 = &a[k..2 * k];
    let a2 = &a[2 * k..];
    let b0 = &b[0..k];
    let b1 = &b[k..2 * k];
    let b2 = &b[2 * k..];

    // Zero only what we use directly, other multiplication routines do the same.
    scratch[..8 * k + 18].fill(0);

    let (eval_buf, scratch) = scratch.split_at_mut(2 * (k + 3));
    let (eval_a, eval_b) = eval_buf.split_at_mut(k + 3);

    /*
     * Originally, we took 2*k and 2*nr digits from scratch for w0 and w4.
     * However, upon observing that results were not assembled into r until the
     * end, we can reduce scratch space by 2*n by using r[..2*k] and
     * r[4*k..4*k+2*nr] directly.
     */
    let (w1_buf, scratch) = scratch.split_at_mut(2 * (k + 2));
    let (w2_buf, scratch) = scratch.split_at_mut(2 * (k + 3));
    let (w3_buf, scratch) = scratch.split_at_mut(2 * (k + 1));

    /*
     *  Evaluation
     */
    /* (1) w0 = a0 * b0 */
    s_mul_aligned(&mut r[..2 * k], a0, b0, scratch);

    /* (2) w1 = (a0 + a1 + a2) * (b0 + b1 + b2) */

    // a0 + a1 + a2
    eval_a[..k].copy_from_slice(a0);
    s_iadd(eval_a, a1);
    s_iadd(eval_a, a2);

    // b0 + b1 + b2
    eval_b[..k].copy_from_slice(b0);
    s_iadd(eval_b, b1);
    s_iadd(eval_b, b2);

    s_mul_aligned(w1_buf, &eval_a[..k + 2], &eval_b[..k + 2], scratch);

    /* (3) w2 = (a0 + 2 * a1 + 4 * a2) * (b0 + 2 * b1 + 4 * b2) */
    eval_a[k..].fill(0);
    eval_b[k..].fill(0);

    // a0 + 2 * a1 + 4 * a2
    eval_a[..k].copy_from_slice(a0);
    s_add_shl(eval_a, a1, 1); // Add 2 * a1
    s_add_shl(eval_a, a2, 2); // Add 4 * a2

    // b0 + 2 * b1 + 4 * b2
    eval_b[..k].copy_from_slice(b0);
    s_add_shl(eval_b, b1, 1); // Add 2 * b1
    s_add_shl(eval_b, b2, 2); // Add 4 * b2

    s_mul_aligned(w2_buf, eval_a, eval_b, scratch);

    /* (4) w3 = ((a0 + a2) - a1) * ((b0 + b2) - b1) */
    eval_a[k..].fill(0);
    eval_b[k..].fill(0);
    let mut w3_is_neg = false;

    // a0 + a2
    eval_a[..k].copy_from_slice(a0);
    s_iadd(eval_a, a2);

    // (a0 + a2) - a1
    let eval_a_len = eval_a.iter().rposition(|&x| x != 0).map_or(1, |i| i + 1);
    match s_cmp(&eval_a[..eval_a_len], a1) {
        Ordering::Less => {
            // |a1| > |a0 + a2|
            s_isub_aligned_from_other(eval_a, a1);
            w3_is_neg = !w3_is_neg;
        }
        Ordering::Equal => {
            eval_a.fill(0);
        }
        Ordering::Greater => {
            s_isub(&mut eval_a[..eval_a_len], a1);
        }
    }

    // b0 + b2
    eval_b[..k].copy_from_slice(b0);
    s_iadd(eval_b, b2);

    // (b0 + b2) - b1
    let eval_b_len = eval_b.iter().rposition(|&x| x != 0).map_or(1, |i| i + 1);
    match s_cmp(&eval_b[..eval_b_len], b1) {
        Ordering::Less => {
            // |b1| > |b0 + b2|
            s_isub_aligned_from_other(eval_b, b1);
            w3_is_neg = !w3_is_neg;
        }
        Ordering::Equal => {
            eval_b.fill(0);
        }
        Ordering::Greater => {
            s_isub(&mut eval_b[..eval_b_len], b1);
        }
    }

    s_mul_aligned(w3_buf, &eval_a[..k + 1], &eval_b[..k + 1], scratch);

    /* (5) w4 = a2 * b2 */
    s_mul_aligned(&mut r[4 * k..4 * k + 2 * nr], a2, b2, scratch);

    /*
     *  Interpolation
     */
    let w0_buf = &r[..2 * k];
    let w4_buf = &r[4 * k..4 * k + 2 * nr];
    let w3p_buf = eval_buf; // 2 * (k + 3)
    let (w1p_buf, _scratch) = scratch.split_at_mut(2 * (k + 3));
    w3p_buf.fill(0);
    w1p_buf.fill(0);

    /* w2 = (w2 - w3)/3 */
    if w3_is_neg {
        // w3 < 0 ==> w2 - (-w3) = w2 + w3
        s_iadd(w2_buf, w3_buf);
    } else {
        // w3 >= 0 ==> w2 - w3
        s_isub(w2_buf, w3_buf);
    }
    s_idivrem_digit(w2_buf, 3);

    /* w3 = (w1 - w3)/2 */
    let w1_len = w1_buf.iter().rposition(|&x| x != 0).map_or(1, |i| i + 1);
    w3p_buf[..w1_len].copy_from_slice(&w1_buf[..w1_len]);
    if w3_is_neg {
        // w3 < 0 ==> w1 - (-w3) = w1 + w3
        s_iadd(w3p_buf, w3_buf);
    } else {
        // w3 >= 0 ==> w1 - w3
        s_isub(w3p_buf, w3_buf);
    }
    s_ishr(w3p_buf, 1);

    /* w1 = (w1 - w0) */
    s_sub(w1p_buf, w1_buf, w0_buf);

    /* w2 = (w2 - w1)/2 */
    s_isub(w2_buf, w1p_buf);
    s_ishr(w2_buf, 1);

    /* w1 = (w1 - w3 - w4) */
    s_isub(w1p_buf, w3p_buf);
    s_isub(w1p_buf, w4_buf);

    /* w2 = (w2 - 2 * w4) */
    s_sub_muldigit(w2_buf, w4_buf, 2);

    /* w3 = (w3 - w2) */
    s_isub(w3p_buf, w2_buf);

    /*
     * Recomposition. w0_buf and w4_buf are already in r[..2*k] and
     * r[4*k..4*k+2*nr], respectively.
     */
    s_iadd(&mut r[k..], w3p_buf);
    s_iadd(&mut r[2 * k..], w1p_buf);
    s_iadd(&mut r[3 * k..], w2_buf);
}

/* Higher-Level Multiplication Routines */

pub(crate) fn s_mul_aligned(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    scratch: &mut [Digit],
) {
    debug_assert_eq!(a.len(), b.len());
    debug_assert!(r.len() >= 2 * a.len());
    if a.len() <= MUL_KARATSUBA_CUTOFF {
        s_mul_gradeschool(r, a, b);
    } else if a.len() <= MUL_TOOMCOOK3_CUTOFF {
        s_mul_karatsuba_aligned(r, a, b, scratch);
    } else {
        s_mul_toomcook3_aligned(r, a, b, scratch);
    }
}

pub(crate) fn s_mul_general(
    r: &mut [Digit],
    a: &[Digit],
    b: &[Digit],
    scratch: &mut [Digit],
) {
    debug_assert!(!a.is_empty() && !b.is_empty());
    debug_assert!(r.len() >= a.len() + b.len());
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    if a.len() == b.len() {
        s_mul_aligned(r, a, b, scratch);
    } else {
        s_mul_gradeschool(r, a, b);
    }
}

impl Arbi {
    pub(crate) fn mul_(r: &mut Arbi, a: &Arbi, b: &Arbi) {
        if a.is_zero() || b.is_zero() {
            r.make_zero();
            return;
        }
        r.vec.clear();
        r.vec.resize(a.size() + b.size(), 0);
        if core::ptr::eq(a, b) {
            let mut scratch = vec![0; square_scratch_size(a.size())];
            s_square(&mut r.vec, &a.vec, &mut scratch);
        } else {
            let (_asize, bsize, a_digits, b_digits) = if a.size() >= b.size() {
                (a.size(), b.size(), &a.vec, &b.vec)
            } else {
                (b.size(), a.size(), &b.vec, &a.vec)
            };
            let mut scratch = vec![0; scratch_size(bsize)];
            s_mul_general(&mut r.vec, a_digits, b_digits, &mut scratch);
        }
        r.neg = a.neg ^ b.neg;
        r.trim();
    }

    pub(crate) fn mul_assign_(&mut self, rhs: &Arbi) {
        if self.is_zero() || rhs.is_zero() {
            self.make_zero();
            return;
        }
        let tmp = self.clone();
        Self::mul_(self, &tmp, rhs);
    }

    pub(crate) fn mul_with_arbi_like_view(
        r: &mut Arbi,
        a: ArbiLikeView,
        b: ArbiLikeView,
    ) {
        if a.is_zero() || b.is_zero() {
            r.make_zero();
            return;
        }
        r.vec.clear();
        r.vec.resize(a.size() + b.size(), 0);
        let (_asize, bsize, a_digits, b_digits) = if a.size() >= b.size() {
            (a.size(), b.size(), &a.vec, &b.vec)
        } else {
            (b.size(), a.size(), &b.vec, &a.vec)
        };
        let mut scratch = vec![0; scratch_size(bsize)];
        s_mul_general(&mut r.vec, a_digits, b_digits, &mut scratch);
        r.neg = a.neg ^ b.neg;
        r.trim();
    }

    /// Multiply this integer in place by a digit and optionally, add a digit
    /// to this integer.
    ///
    /// This function does not trim trailing zeros in the digit vector.
    ///
    /// Knuth Algorithm M, but recognizing
    /// 1. \\( j \\) is always 0
    /// 2. \\( w\_{i + j} = w\_{i} \\) is always zero when forming \\( t \\).
    /// 3. We can safely make the initial carry nonzero to implement adding a
    ///    digit.
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    #[inline(always)]
    pub(crate) fn imul1add1(x: &mut Self, v: Digit, k: Option<Digit>) {
        let mut k: Digit = k.unwrap_or(0);
        for d in &mut x.vec {
            let t: DDigit = (*d as DDigit) * (v as DDigit) + (k as DDigit);
            k = (t >> Digit::BITS) as Digit; // floor(t / 2^{Digit::BITS})
            *d = t as Digit; // t mod 2^{Digit::BITS}
        }
        if k != 0 {
            x.vec.push(k);
        }
    }
}
