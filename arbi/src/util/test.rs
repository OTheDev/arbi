/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/* Utilities for testing. */

#[cfg(test)]
extern crate std;

use std::println;

use crate::Base;
use crate::{Arbi, Digit};
use rand::distributions::uniform::SampleUniform;
pub(crate) use rand::distributions::Distribution;
pub use rand::distributions::Uniform;
use rand::rngs::{StdRng, ThreadRng};
pub(crate) use rand::Rng;
use rand::SeedableRng;

pub(crate) const BASE10: Base = crate::base::BASE10;

pub(crate) fn get_seedable_rng() -> (StdRng, u64) {
    let mut rng = rand::thread_rng();
    let seed: u64 = rng.gen();
    println!("Generated seed: {}", seed);
    (StdRng::seed_from_u64(seed), seed)
}

fn get_rng() -> ThreadRng {
    rand::thread_rng()
}

pub(crate) fn get_uniform_die<T: SampleUniform>(
    min_inclusive: T,
    max_inclusive: T,
) -> Uniform<T> {
    Uniform::from(min_inclusive..=max_inclusive)
}

pub(crate) fn random_arbi(z: usize) -> Arbi {
    let mut result = Arbi::zero();
    if z == 0 {
        return result;
    }

    let mut num_digits: usize = z / Digit::BITS as usize;
    let remainder: usize = z % Digit::BITS as usize;

    if remainder != 0 {
        num_digits += 1;
    }

    result.vec.resize(num_digits, 0);

    let mut rng = get_rng();
    let die = get_uniform_die(Digit::MIN, Digit::MAX);
    for i in 0..(num_digits - 1) {
        result.vec[i] = die.sample(&mut rng);
    }

    if remainder != 0 {
        let mask: Digit = ((1 as Digit) << remainder) - 1;
        result.vec[num_digits - 1] = die.sample(&mut rng) & mask;
    } else {
        result.vec[num_digits - 1] = die.sample(&mut rng);
    }

    result.trim();

    result
}

pub(crate) fn ldexp(x: f64, exp: i32) -> f64 {
    x * 2_f64.powi(exp)
}

#[allow(dead_code)]
pub(crate) mod float {
    pub(crate) const ZERO: f64 = 0.0;
    pub(crate) const MAX_INT: f64 = 9007199254740992.0; // 2^53
    pub(crate) const DBL_MAX_INT: u64 = 1 << 53;
    pub(crate) const MAX_INT_NEG: f64 = -9007199254740992.0;
    pub(crate) const LOWEST_DOUBLE: f64 = f64::MIN;
    pub(crate) const MAX_DOUBLE: f64 = f64::MAX;
    pub(crate) const MIN_DOUBLE: f64 = f64::MIN_POSITIVE;
    pub(crate) const SUBNORMAL_DOUBLE: f64 =
        f64::MIN_POSITIVE / (1u64 << 52) as f64;
    pub(crate) const INF: f64 = f64::INFINITY;
    pub(crate) const MINF: f64 = f64::NEG_INFINITY;
    pub(crate) const NAN: f64 = f64::NAN;

    pub(crate) fn assert_double_eq(a: f64, b: f64) {
        const MAX_ULPS: u64 = 4;

        let a_bits = a.to_bits() as i64;
        let b_bits = b.to_bits() as i64;

        if a.is_nan() || b.is_nan() {
            panic!("Comparison with NaN");
        }

        let ulp_difference = (a_bits - b_bits).unsigned_abs();
        if ulp_difference > MAX_ULPS {
            panic!(
                "Values are not approximately equal: {} and {}, ULP difference: {}",
                a, b, ulp_difference
            )
        }
    }
}
