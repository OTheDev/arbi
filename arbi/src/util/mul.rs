/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

macro_rules! define_mul2_internal {
    // Internal macro that defines the common parts
    ($uint:ty) => {
        const UINT_BITS: u32 = <$uint>::BITS;
        const UINT_H_BITS: u32 = UINT_BITS >> 1;
        const UINT_H_BASE: $uint = 1 as $uint << UINT_H_BITS;
        const UINT_H_MAX: $uint = UINT_H_BASE - 1;

        #[inline(always)]
        #[allow(dead_code)]
        const fn split_uint(x: $uint) -> ($uint, $uint) {
            let hi = x >> UINT_H_BITS;
            let lo = x & UINT_H_MAX;
            (hi, lo)
        }

        #[inline]
        #[allow(dead_code)]
        pub(crate) const fn mul2(a: $uint, b: $uint) -> ($uint, $uint) {
            let (a_hi, a_lo) = split_uint(a);
            let (b_hi, b_lo) = split_uint(b);

            let mut ahbh = a_hi * b_hi;
            let ahbl = a_hi * b_lo;
            let mut albh = a_lo * b_hi;
            let albl = a_lo * b_lo;

            let (albl_hi, albl_lo) = split_uint(albl);

            albh += albl_hi;
            debug_assert!(albh >= albl_hi);

            let (albh, overflow) = albh.overflowing_add(ahbl);
            if overflow {
                ahbh = ahbh.wrapping_add(UINT_H_BASE);
            }

            (
                ahbh.wrapping_add(albh >> UINT_H_BITS),
                albl_lo.wrapping_add(albh << UINT_H_BITS),
            )
        }
    };
}

macro_rules! define_mul2 {
    // Single parameter version - only defines mul2()
    ($uint:ty) => {
        define_mul2_internal!($uint);
    };

    // Two parameter version - adds mul2_halves()
    ($uint:ty, $uint_h:ty) => {
        define_mul2_internal!($uint);

        #[inline(always)]
        const fn split_uint_halves(x: $uint) -> ($uint_h, $uint_h) {
            let hi = (x >> UINT_H_BITS) as $uint_h;
            let lo = (x & UINT_H_MAX) as $uint_h;
            (hi, lo)
        }

        #[inline]
        pub(crate) const fn mul2_halves(a: $uint, b: $uint) -> ($uint, $uint) {
            let (a_hi, a_lo) = split_uint_halves(a);
            let (b_hi, b_lo) = split_uint_halves(b);

            let mut ahbh: $uint = (a_hi as $uint) * (b_hi as $uint);
            let ahbl: $uint = (a_hi as $uint) * (b_lo as $uint);
            let mut albh: $uint = (a_lo as $uint) * (b_hi as $uint);
            let albl: $uint = (a_lo as $uint) * (b_lo as $uint);

            let (albl_hi, albl_lo) = split_uint_halves(albl);

            albh += albl_hi as $uint;
            debug_assert!(albh >= albl_hi as $uint);

            let (albh, overflow) = albh.overflowing_add(ahbl);
            if overflow {
                ahbh = ahbh.wrapping_add(UINT_H_BASE);
            }

            (
                ahbh.wrapping_add(albh >> UINT_H_BITS),
                (albl_lo as $uint).wrapping_add(albh << UINT_H_BITS),
            )
        }
    };
}

// macro_rules! define_mul2 {
//     // mul2(), mul2_halves() implement
//     //
//     //      a * b -> (hi, lo)
//     //
//     //      where a, b, hi, lo are all of type uint.
//     //
//     // They are equivalent in behavior.
//     //
//     // uint     : primitive unsigned integer type (e.g. u128).
//     // uint_h   : primitive unsigned integer type with size in bits half that
//     //            of uint.
//     ($uint:ty, $uint_h:ty) => {

// const UINT_BITS: u32 = <$uint>::BITS;
// const UINT_H_BITS: u32 = UINT_BITS >> 1;
// const UINT_H_BASE: $uint = 1 as $uint << UINT_H_BITS;
// const UINT_H_MAX: $uint = UINT_H_BASE - 1; // MASK for low part of UINT

// #[inline(always)]
// #[allow(dead_code)]
// const fn split_uint(x: $uint) -> ($uint, $uint) {
//     let hi = x >> UINT_H_BITS;
//     let lo = x & UINT_H_MAX;
//     (hi, lo)
// }

// #[inline(always)]
// const fn split_uint_halves(x: $uint) -> ($uint_h, $uint_h) {
//     let hi = (x >> UINT_H_BITS) as $uint_h;
//     let lo = (x & UINT_H_MAX) as $uint_h;
//     (hi, lo)
// }

// #[inline]
// #[allow(dead_code)]
// pub(crate) const fn mul2(a: $uint, b: $uint) -> ($uint, $uint) {
//     let (a_hi, a_lo) = split_uint(a);
//     let (b_hi, b_lo) = split_uint(b);

//     let mut ahbh = a_hi * b_hi;
//     let ahbl = a_hi * b_lo;
//     let mut albh = a_lo * b_hi;
//     let albl = a_lo * b_lo;

//     let (albl_hi, albl_lo) = split_uint(albl);

//     albh += albl_hi;
//     debug_assert!(albh >= albl_hi);

//     let (albh, overflow) = albh.overflowing_add(ahbl);
//     if overflow {
//         ahbh = ahbh.wrapping_add(UINT_H_BASE);
//     }

//     (
//         ahbh.wrapping_add(albh >> UINT_H_BITS),
//         albl_lo.wrapping_add(albh << UINT_H_BITS),
//     )
// }

// #[inline]
// pub(crate) const fn mul2_halves(a: $uint, b: $uint) -> ($uint, $uint) {
//     let (a_hi, a_lo) = split_uint_halves(a);
//     let (b_hi, b_lo) = split_uint_halves(b);

//     let mut ahbh: $uint = (a_hi as $uint) * (b_hi as $uint);
//     let ahbl: $uint = (a_hi as $uint) * (b_lo as $uint);
//     let mut albh: $uint = (a_lo as $uint) * (b_hi as $uint);
//     let albl: $uint = (a_lo as $uint) * (b_lo as $uint);

//     let (albl_hi, albl_lo) = split_uint_halves(albl);

//     albh += albl_hi as $uint;
//     debug_assert!(albh >= albl_hi as $uint);

//     let (albh, overflow) = albh.overflowing_add(ahbl);
//     if overflow {
//         ahbh = ahbh.wrapping_add(UINT_H_BASE);
//     }

//     (
//         ahbh.wrapping_add(albh >> UINT_H_BITS),
//         (albl_lo as $uint).wrapping_add(albh << UINT_H_BITS),
//     )
// }

//     };
// }

pub(crate) mod u128_impl {
    define_mul2!(u128, u64);
}

#[allow(dead_code)]
mod u64_impl {
    define_mul2!(u64, u32);
}

pub(crate) mod usize_impl {
    define_mul2!(usize);
}

/* TODO: clean up and reduce repetition */
#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_u128_implementations() {
        let test_values = [
            0u128,
            1u128,
            2u128,
            3u128,
            u128::MAX,
            1u128 << 127,
            (1u128 << 64) - 1,
            1u128 << 64,
        ];

        for a in test_values {
            for b in test_values {
                let r1 = u128_impl::mul2(a, b);
                let r2 = u128_impl::mul2_halves(a, b);
                assert_eq!(r1, r2,
                    "Results differ for u128 inputs {} and {}: basic: {:?} vs half: {:?}",
                    a, b, r1, r2);
            }
        }

        use crate::Arbi;
        let mut rng = rand::thread_rng();
        for _ in 0..i16::MAX {
            let a: u128 = rng.gen();
            let b: u128 = rng.gen();

            let (hi, lo) = u128_impl::mul2(a, b);

            // Verify using Arbi integers
            let res = Arbi::from(a) * Arbi::from(b);
            let expected_lo = res.wrapping_to_u128(); // truncates
            let expected_hi = (res >> 128u32).checked_to_u128().unwrap();

            assert_eq!((hi, lo), (expected_hi, expected_lo),
                "Mismatch for inputs {} and {}\nGot: ({}, {})\nExpected: ({}, {})",
                a, b, hi, lo, expected_hi, expected_lo);

            let halves_res = u128_impl::mul2_halves(a, b);
            assert_eq!(halves_res, (expected_hi, expected_lo),
                "Halves implementation mismatch for inputs {} and {}\nGot: ({}, {})\nExpected: ({}, {})",
                a, b, halves_res.0, halves_res.1, expected_hi, expected_lo);
        }
    }

    #[test]
    fn test_u64_implementations() {
        let test_values = [
            0u64,
            1u64,
            2u64,
            3u64,
            u64::MAX,
            1u64 << 63,
            (1u64 << 32) - 1,
            1u64 << 32,
        ];

        for a in test_values {
            for b in test_values {
                let r1 = u64_impl::mul2(a, b);
                let r2 = u64_impl::mul2_halves(a, b);
                assert_eq!(r1, r2,
                    "Results differ for u64 inputs {} and {}: basic: {:?} vs half: {:?}",
                    a, b, r1, r2);
            }
        }

        let mut rng = rand::thread_rng();
        for _ in 0..i16::MAX {
            let a: u64 = rng.gen();
            let b: u64 = rng.gen();

            let (hi, lo) = u64_impl::mul2(a, b);

            // "native" u128 multiplication
            let res = (a as u128) * (b as u128);
            let expected_hi = (res >> 64) as u64;
            let expected_lo = res as u64;

            assert_eq!((hi, lo), (expected_hi, expected_lo),
                "Mismatch for inputs {} and {}\nGot: ({}, {})\nExpected: ({}, {})",
                a, b, hi, lo, expected_hi, expected_lo);

            let halves_res = u64_impl::mul2_halves(a, b);
            assert_eq!(halves_res, (expected_hi, expected_lo),
                "Halves implementation mismatch for inputs {} and {}\nGot: ({}, {})\nExpected: ({}, {})",
                a, b, halves_res.0, halves_res.1, expected_hi, expected_lo);
        }
    }
}
