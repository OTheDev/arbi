/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use super::impls::{s_mul_karatsuba_aligned, s_mul_toomcook3_aligned};
use super::{MUL_SQUARE_KARATSUBA_CUTOFF, MUL_SQUARE_TOOMCOOK3_CUTOFF};
use crate::uints::UnsignedUtilities;
use crate::{DDigit, Digit};

/* TODO: when do we choose Karatsuba over gradeschool and Toom-Cook over
 * Karatsuba?
 */
pub(crate) fn s_square(w: &mut [Digit], a: &[Digit], scratch: &mut [Digit]) {
    debug_assert!(w.len() >= 2 * a.len());
    if a.len() <= MUL_SQUARE_KARATSUBA_CUTOFF {
        s_square_quadratic(w, a);
    } else if a.len() <= MUL_SQUARE_TOOMCOOK3_CUTOFF {
        s_mul_karatsuba_aligned(w, a, a, scratch);
    } else {
        s_mul_toomcook3_aligned(w, a, a, scratch);
    }
}

// Algorithm 14.16 from Handbook of Applied Cryptography (1996)
pub(crate) fn s_square_quadratic(w: &mut [Digit], a: &[Digit]) {
    debug_assert!(w.len() >= 2 * a.len());
    let t = a.len();
    w.fill(0);
    let mut c: DDigit;
    for i in 0..t {
        if Digit::BITS == 32 {
            type QDigit = u128;
            let uv: QDigit =
                w[2 * i] as QDigit + a[i] as QDigit * a[i] as QDigit;
            w[2 * i] = uv as Digit; // set w[2 * i] <- v
            c = (uv >> Digit::BITS) as DDigit; // set c <- u
            for j in (i + 1)..t {
                let uv: QDigit = 2 * a[j] as QDigit * a[i] as QDigit
                    + w[i + j] as QDigit
                    + c as QDigit;
                w[i + j] = uv as Digit; // set w[i + j] <- v
                c = (uv >> Digit::BITS) as DDigit; // set c <- u
            }
        } else if Digit::BITS == 64 {
            // This works for the 32-bit case as well.
            let uv: DDigit =
                w[2 * i] as DDigit + a[i] as DDigit * a[i] as DDigit;
            w[2 * i] = uv as Digit; // set w[2 * i] <- v
            c = uv >> Digit::BITS; // set c <- u
            for j in (i + 1)..t {
                // (hi, lo) represents a quadruple digit
                let mut lo: DDigit = a[j] as DDigit * a[i] as DDigit;
                // Multiply product by two
                let mut hi = lo >> (DDigit::BITS - 1);
                lo <<= 1;
                // Now add w[i + j] and c to (hi, lo)
                let mut lo_clone = lo;
                let overflow = DDigit::uadd_overflow(
                    &mut lo,
                    lo_clone,
                    w[i + j] as DDigit,
                );
                hi += DDigit::from(overflow);
                lo_clone = lo;
                let overflow = DDigit::uadd_overflow(&mut lo, lo_clone, c);
                hi += DDigit::from(overflow);
                // Collect
                w[i + j] = lo as Digit; // set w[i + j] <- v
                c = (hi << Digit::BITS) | (lo >> Digit::BITS); // set c <- u
            }
        } else {
            unreachable!("Digit::BITS must be 32 or 64.");
        }
        let mut k = i + t;
        while c > 0 {
            c += w[k] as DDigit;
            w[k] = c as Digit;
            c >>= Digit::BITS;
            k += 1;
        }
    }
}
