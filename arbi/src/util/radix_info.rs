/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::mul::{u128_impl, usize_impl};
use crate::{Arbi, BitCount, DDigit, Digit};

/*
Given an n-digit integer in base b, the largest integer representable is

\\[
    b^{n} - 1
\\]

The minimum number of base b digits, n, required to represent any
m-digit base c integer is such that:

\\[
    \begin{align}
        b^{n} - 1                 & \geq c^{m} - 1                          \\\\
        b^{n}                     & \geq c^{m}                              \\\\
        \frac{b^{n}}{c^{m}}       & \geq 1                                  \\\\
        \log(b^{n}) - \log(c^{m}) & \geq 0                                  \\\\
        n                         & \geq m \cdot \frac{\log(c)}{\log(b)}
    \end{align}
\\]
*/

impl Arbi {
    /*
    SCALED_LOG2_DIV_LOG:

        ceil( (log(2) / log(base)) * 2^(Digit::BITS) )

    SCALED_LOG2_DIV_LOG_64 (not used):

        ceil( (log(2) / log(base)) * 2^(64) )

    All platforms currently use 32 as Digit::BITS, but in the future, we may
    choose to use 64 for some platforms, in which case the values in the latter
    array will be used.

    The values in both arrays were precomputed via a Python script using
    Python `decimal.Decimal` objects. See scripts/size_in_radix.py.

    Technically, the results in the former array can be accurately computed
    simply using f64s. However, f64s won't give us accurate values for the
    latter array, due to precision issues. More complicated methods with the
    help of u128s can be used for the former, but higher width integers (like
    Arbi integers) would be needed for the latter.
    */
    /// ceil( (log(2) / log(base)) * 2^(32) )
    #[cfg(not(target_pointer_width = "64"))]
    const SCALED_LOG2_DIV_LOG: [u32; 37] = [
        0x00000000, 0x00000000, 0x00000000, 0xa1849cc2, 0x80000000, 0x6e40d1a5,
        0x6308c91c, 0x5b3064ec, 0x55555556, 0x50c24e61, 0x4d104d43, 0x4a002708,
        0x4768ce0e, 0x452e53e4, 0x433cfffc, 0x41867712, 0x40000000, 0x3ea16afe,
        0x3d64598e, 0x3c43c231, 0x3b3b9a43, 0x3a4898f1, 0x39680b14, 0x3897b2b8,
        0x37d5aed2, 0x372068d3, 0x3676867f, 0x35d6deec, 0x354071d7, 0x34b260c6,
        0x342be987, 0x33ac61ba, 0x33333334, 0x32bfd902, 0x3251dcf7, 0x31e8d5a0,
        0x3184648e,
    ];

    /// ceil( (log(2) / log(base)) * 2^(64) )
    #[allow(dead_code)]
    #[cfg(target_pointer_width = "64")]
    const SCALED_LOG2_DIV_LOG: [u64; 37] = [
        0x0000000000000000,
        0x0000000000000000,
        0x0000000000000000,
        0xa1849cc1a9a9e94f,
        0x8000000000000000,
        0x6e40d1a4143dcb95,
        0x6308c91b702a7cf5,
        0x5b3064eb3aa6d389,
        0x5555555555555556,
        0x50c24e60d4d4f4a8,
        0x4d104d427de7fbcd,
        0x4a00270775914e89,
        0x4768ce0d05818e13,
        0x452e53e365907bdb,
        0x433cfffb4b5aae56,
        0x41867711b4f85356,
        0x4000000000000000,
        0x3ea16afd58b10967,
        0x3d64598d154dc4df,
        0x3c43c23018bb5564,
        0x3b3b9a42873069c8,
        0x3a4898f06cf41aca,
        0x39680b13582e7c19,
        0x3897b2b751ae561b,
        0x37d5aed131f19c99,
        0x372068d20a1ee5cb,
        0x3676867e5d60de2a,
        0x35d6deeb388df870,
        0x354071d61c77fa2f,
        0x34b260c5671b18ad,
        0x342be986572b45cd,
        0x33ac61b998fbbdf3,
        0x3333333333333334,
        0x32bfd90114c12862,
        0x3251dcf6169e45f3,
        0x31e8d59f180dc631,
        0x3184648db8153e7b,
    ];

    /// Compute the number of base-`base` digits needed to represent a
    /// nonnegative integer with `size_bits` bits. The true value or one higher
    /// than it will be returned.
    ///
    /// # Panic
    /// This function panics if `base` is not in the half-open interval
    /// `(2, 36]`, or if `size_bits` is `0`.
    #[inline]
    pub(crate) const fn size_base_with_size_bits_maybe_over_by_one(
        base: u32,
        size_bits: BitCount,
    ) -> BitCount {
        assert!(base > 2 && base <= 36, "base must be in (2, 36]");
        assert!(size_bits != 0);

        let multiplicand = Self::SCALED_LOG2_DIV_LOG[base as usize] as BitCount;

        if let Some(product) = size_bits.checked_mul(multiplicand) {
            product >> Digit::BITS
        } else {
            /* Multiplication overflowed, so we do it again, this time storing
             * the product in a 256-bit unsigned integer (represented as two
             * u128s). */
            let (hi, lo) = u128_impl::mul2_halves(size_bits, multiplicand);

            /* Now shift the product right by Digit::BITS */
            debug_assert!(hi >> Digit::BITS == 0);
            (hi << (u128::BITS - Digit::BITS)) | (lo >> Digit::BITS)
        }
        .wrapping_add(1)
    }

    /// ceil( (log(base) / log(2^(32))) * 2^(32) )
    #[cfg(not(target_pointer_width = "64"))]
    const SCALED_LOGB_DIV_LOGAB: [u32; 37] = [
        0x00000000, 0x00000000, 0x8000000, 0xcae00d2, 0x10000000, 0x12934f0a,
        0x14ae00d2, 0x16757680, 0x18000001, 0x195c01a4, 0x1a934f0a, 0x1bacea7d,
        0x1cae00d2, 0x1d9a8024, 0x1e757680, 0x1f414fdc, 0x20000000, 0x20b31fb8,
        0x215c01a4, 0x21fbc16c, 0x22934f0a, 0x23237752, 0x23acea7d, 0x24304141,
        0x24ae00d2, 0x25269e13, 0x259a8024, 0x260a0276, 0x26757680, 0x26dd2524,
        0x27414fdc, 0x27a231ad, 0x28000000, 0x285aeb4e, 0x28b31fb8, 0x2908c589,
        0x295c01a4,
    ];

    #[allow(dead_code)]
    /// ceil( (log(base) / log(2^(64))) * 2^(64) )
    #[cfg(target_pointer_width = "64")]
    const SCALED_LOGB_DIV_LOGAB: [u64; 37] = [
        0x0000000000000000,
        0x0000000000000000,
        0x400000000000000,
        0x6570068e7ef5a1f,
        0x800000000000000,
        0x949a784bcd1b8b0,
        0xa570068e7ef5a1f,
        0xb3abb3faa02166d,
        0xc00000000000001,
        0xcae00d1cfdeb43d,
        0xd49a784bcd1b8b0,
        0xdd6753e032ea0f0,
        0xe570068e7ef5a1f,
        0xecd4011c8f1197a,
        0xf3abb3faa02166d,
        0xfa0a7eda4c112cf,
        0x1000000000000000,
        0x10598fdbeb244c5a,
        0x10ae00d1cfdeb43d,
        0x10fde0b5c8134052,
        0x1149a784bcd1b8b0,
        0x1191bba891f1708c,
        0x11d6753e032ea0f0,
        0x121820a01ac754cc,
        0x12570068e7ef5a1f,
        0x12934f0979a37160,
        0x12cd4011c8f1197a,
        0x1305013ab7ce0e5c,
        0x133abb3faa02166d,
        0x136e9291eaa65b4a,
        0x13a0a7eda4c112cf,
        0x13d118d66c4d4e56,
        0x1400000000000000,
        0x142d75a6eb1dfb0f,
        0x14598fdbeb244c5a,
        0x148462c466d3cf1d,
        0x14ae00d1cfdeb43d,
    ];

    /// Compute the number of base-`Arbi::BASE` digits needed to represent a
    /// nonnegative integer with `size_base` `base` digits. The true value or
    /// one higher than it will be returned.
    ///
    /// # Panic
    /// This function panics if `base` is not in the closed interval `[2, 36]`,
    /// or if `size_base` is `0`.
    #[inline]
    pub(crate) const fn size_with_size_base_maybe_over_by_one(
        base: u32,
        size_base: usize,
    ) -> usize {
        assert!(base >= 2 && base <= 36, "base must be in [2, 36]");
        assert!(size_base != 0);

        /*
           TODO: is this even worth it? The code after this block suffices for
           this case as well.
        */
        if base.is_power_of_two() {
            // This will always be exact for base 2, 4, and 16, but may be off
            // by 1 for base 8 or 32.
            let base_log2 = base.trailing_zeros();
            let bit_length = size_base as BitCount * base_log2 as BitCount;
            return crate::uints::div_ceil_bitcount(
                bit_length,
                Digit::BITS as BitCount,
            ) as usize;
        }

        let multiplicand: Digit = Self::SCALED_LOGB_DIV_LOGAB[base as usize];

        if Digit::BITS >= usize::BITS {
            let product = (size_base as DDigit) * (multiplicand as DDigit);
            (product >> Digit::BITS) as usize
        } else {
            let (hi, lo) = usize_impl::mul2(size_base, multiplicand as usize);

            // To appease rustc-1.65
            let shift = Digit::BITS;
            if shift < usize::BITS {
                debug_assert!(hi >> shift == 0);
                (hi << (usize::BITS - shift)) | (lo >> shift)
            } else {
                unreachable!()
            }
        }
        .wrapping_add(1)
    }
}

#[cfg(test)]
mod tests_size_base_with_size_bits {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, Digit, QDigit};

    fn size_base(mut x: u128, base: u32) -> BitCount {
        if x == 0 {
            return 0;
        }
        let mut count = 0;
        while x > 0 {
            x /= base as u128;
            count += 1;
        }
        count
    }

    fn size_bits(x: u128) -> BitCount {
        (u128::BITS - x.leading_zeros()).into()
    }

    fn size_base_big(mut x: QDigit, base: u32) -> BitCount {
        let base = QDigit::from(base);
        if x == QDigit::from(0) {
            return 0;
        }
        let mut count: BitCount = 0;
        while x > QDigit::from(0) {
            x /= base;
            count += 1;
        }
        count
    }

    fn size_bits_big(x: QDigit) -> BitCount {
        (QDigit::BITS as u32 - x.leading_zeros() as u32).into()
    }

    #[test]
    fn test_random_integers() {
        let (mut rng, _) = get_seedable_rng();
        let d1 = get_uniform_die(0, Digit::MAX);
        let d2 = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        for _ in 0..i16::MAX {
            let nums =
                [d1.sample(&mut rng) as u128, d2.sample(&mut rng) as u128];
            for num in nums {
                let bits = size_bits(num);
                for base in 3..=36 {
                    let estimated =
                        Arbi::size_base_with_size_bits_maybe_over_by_one(
                            base, bits,
                        );
                    let actual = size_base(num, base);
                    assert!(
                        estimated == actual || estimated == actual + 1,
                        "Failed for num={}, base={}: estimated={}, actual={}, bits={}",
                        num, base, estimated, actual, bits
                    );
                }
            }
        }
    }

    #[test]
    fn smoke_size_with_size_base() {
        let (mut rng, _) = get_seedable_rng();
        let d1 = get_uniform_die(0, Digit::MAX);
        let d2 = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        for _ in 0..i16::MAX {
            let nums =
                [d1.sample(&mut rng) as u128, d2.sample(&mut rng) as u128];
            for num in nums {
                if num == 0 {
                    continue;
                }
                let arbi = Arbi::from(num);
                let actual = arbi.size();
                for base in 2..=36 {
                    let sz_base = size_base(num, base) as usize;
                    let estimated = Arbi::size_with_size_base_maybe_over_by_one(
                        base, sz_base,
                    );
                    assert!(
                        estimated == actual || estimated == actual + 1,
                        "arbi = {}, estimate = {}, actual = {}, base = {}",
                        arbi,
                        estimated,
                        actual,
                        base
                    );
                }
            }
        }
    }

    #[test]
    fn test_random_integers_big() {
        let (mut rng, _) = get_seedable_rng();
        let d3 = crate::util::qdigit::get_uniform_qdigit_die(
            QDigit::from(DDigit::MAX) + QDigit::from(1),
            QDigit::MAX,
        );
        for _ in 0..i16::MAX {
            let nums = [d3.sample(&mut rng)];
            for num in nums {
                let bits = size_bits_big(num);
                for base in 3..=36 {
                    let estimated =
                        Arbi::size_base_with_size_bits_maybe_over_by_one(
                            base, bits,
                        );
                    let actual = size_base_big(num, base);
                    assert!(
                        estimated == actual || estimated == actual + 1,
                        "Failed for num={}, base={}: estimated={}, actual={}, bits={}",
                        num, base, estimated, actual, bits
                    );
                }
            }
        }
    }

    #[test]
    fn smoke_size_with_size_base_big() {
        let (mut rng, _) = get_seedable_rng();
        let d3 = crate::util::qdigit::get_uniform_qdigit_die(
            QDigit::from(DDigit::MAX) + QDigit::from(1),
            QDigit::MAX,
        );
        for _ in 0..i16::MAX {
            let nums = [d3.sample(&mut rng)];
            for num in nums {
                if num == QDigit::from(0) {
                    continue;
                }
                let arbi = Arbi::from(num);
                let actual = arbi.size();
                for base in 2..=36 {
                    let sz_base = size_base_big(num, base) as usize;
                    let estimated = Arbi::size_with_size_base_maybe_over_by_one(
                        base, sz_base,
                    );
                    assert!(
                        estimated == actual || estimated == actual + 1,
                        "arbi = {}, estimate = {}, actual = {}, base = {}",
                        arbi,
                        estimated,
                        actual,
                        base
                    );
                }
            }
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn smoke_size_with_size_base_large() {
        use crate::{Arbi, RandomArbi};

        let (mut rng, _) = get_seedable_rng();

        for _ in 0..1000 {
            let arbi = rng.gen_iarbi(2420);
            if arbi == 0 {
                continue;
            }
            let actual = arbi.size();
            for base in 2..=36 {
                let arbi_string = arbi.to_string_radix(base);
                let sz_base = if arbi.is_negative() {
                    arbi_string.len() - 1
                } else {
                    arbi_string.len()
                };
                /* TODO: this should not be slower than to_string()... */
                // let sz_base = arbi.size_base_ref(base) as usize;
                let estimated =
                    Arbi::size_with_size_base_maybe_over_by_one(base, sz_base);
                assert!(
                    estimated == actual || estimated == actual + 1,
                    "arbi = {}, estimate = {}, actual = {}, base = {}",
                    arbi,
                    estimated,
                    actual,
                    base
                );
            }
        }
    }
}
