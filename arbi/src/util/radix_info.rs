/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::mul::u128_impl;
use crate::{Arbi, BitCount, Digit};

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
    Python `decimal.Decimal` objects.

    Technically, the results in the former array can be accurately computed
    simply using f64s. However, f64s won't give us accurate values for the
    latter array, due to precision issues. More complicated methods with the
    help of u128s can be used for the former, but higher width integers (like
    Arbi integers) would be needed for the latter.
    */
    /// ceil( (log(2) / log(base)) * 2^(Digit::BITS) )
    const SCALED_LOG2_DIV_LOG: [Digit; 37] = [
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
    const SCALED_LOG2_DIV_LOG_64: [u64; 37] = [
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

    #[test]
    fn test_random_integers() {
        let (mut rng, _) = get_seedable_rng();
        let d1 = get_uniform_die(0, Digit::MAX);
        let d2 = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let d3 = get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let nums = [
                d1.sample(&mut rng) as u128,
                d2.sample(&mut rng) as u128,
                d3.sample(&mut rng) as u128,
            ];

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
}
