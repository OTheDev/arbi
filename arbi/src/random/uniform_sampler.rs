/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

// See https://docs.rs/rand/0.8.5/rand/distributions/uniform/index.html#extending-uniform-to-support-a-custom-type

use crate::{Arbi, RandomArbi};
use rand::distributions::uniform::{
    SampleBorrow, SampleUniform, UniformSampler,
};
use rand::Rng;

#[derive(Debug, Clone)]
pub struct UniformArbi {
    // Instead of the following representation, we could just store lo, hi.
    // However, that approach leads to more memory allocations.
    lower: Arbi,
    delta: Arbi,
}

impl UniformSampler for UniformArbi {
    type X = Arbi;

    fn new<B1, B2>(lo_incl: B1, hi_excl: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let lo_b: &Arbi = lo_incl.borrow();
        let hi_b: &Arbi = hi_excl.borrow();
        assert!(lo_b < hi_b);
        UniformArbi {
            lower: lo_b.clone(),
            delta: hi_b - lo_b,
        }
    }

    fn new_inclusive<B1, B2>(lo_incl: B1, hi_incl: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let lo_b: &Arbi = lo_incl.borrow();
        let hi_b: &Arbi = hi_incl.borrow();
        assert!(lo_b <= hi_b);
        let mut hi = hi_b.clone();
        hi.incr();
        UniformArbi {
            lower: lo_b.clone(),
            delta: hi - lo_b,
        }
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        &self.lower + rng.gen_uarbi_under(&self.delta)
    }

    fn sample_single<R: Rng + ?Sized, B1, B2>(
        lo_incl: B1,
        hi_excl: B2,
        rng: &mut R,
    ) -> Self::X
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let lo: &Arbi = lo_incl.borrow();
        let hi: &Arbi = hi_excl.borrow();
        assert!(lo < hi);
        rng.gen_arbi_range(lo, hi)
    }
}

impl SampleUniform for Arbi {
    type Sampler = UniformArbi;
}

#[cfg(test)]
mod test_uniform_sampler {
    use crate::{Arbi, DDigit, QDigit};
    use rand::distributions::uniform::Uniform;
    use rand::distributions::Distribution;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    #[test]
    #[should_panic]
    fn test_new_panics_on_invalid_range() {
        let (low, high) = (Arbi::from(DDigit::MAX), Arbi::from(DDigit::MAX));
        let _ = Uniform::new(&low, &high);
    }

    #[test]
    #[should_panic]
    fn test_new_inclusive_panics_on_invalid_range() {
        let (low, high) = (
            Arbi::from(DDigit::MAX as QDigit + 1),
            Arbi::from(DDigit::MAX),
        );
        let _ = Uniform::new_inclusive(&low, &high);
    }

    #[test]
    fn test_uniform_repeated() {
        let mut rng = StdRng::seed_from_u64(42);
        // -(2**256 - 1)
        let lower = Arbi::from_str_radix(
            "-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        // -(2**128 - 1)
        let mut upper = Arbi::from(u128::MAX);
        upper.negate_mut();
        let mid = Arbi::from_str_radix(
            "-800000000000000000000000000000007fffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let uniform = Uniform::new(&lower, &upper);
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..(i16::MAX >> 1) {
            let arbi = uniform.sample(&mut rng);
            assert!(arbi >= lower && arbi < upper);
            if arbi > mid {
                num_above += 1;
            } else if arbi < mid {
                num_below += 1;
            }
        }
        let ratio = num_above as f64 / num_below as f64;
        assert!(0.95 < ratio && ratio < 1.05);
    }

    #[test]
    fn test_uniform_inclusive_repeated() {
        let mut rng = StdRng::seed_from_u64(42);
        // 2**128 - 1
        let lower = Arbi::from(u128::MAX);
        // 2**256 - 1
        let upper = Arbi::from_str_radix(
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let mid = Arbi::from_str_radix(
            "800000000000000000000000000000007fffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let uniform = Uniform::new_inclusive(&lower, &upper);
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..(i16::MAX >> 1) {
            let arbi = uniform.sample(&mut rng);
            assert!(arbi >= lower && arbi <= upper);
            if arbi > mid {
                num_above += 1;
            } else if arbi < mid {
                num_below += 1;
            }
        }
        let ratio = num_above as f64 / num_below as f64;
        assert!(0.95 < ratio && ratio < 1.05);
    }

    #[test]
    #[should_panic]
    fn test_sample_single_panics_on_invalid_range() {
        use rand::distributions::uniform::{SampleUniform, UniformSampler};
        let mut rng = StdRng::seed_from_u64(42);
        let (low, high) = (Arbi::from(DDigit::MAX), Arbi::from(DDigit::MAX));
        let _ = <Arbi as SampleUniform>::Sampler::sample_single(
            &low, &high, &mut rng,
        );
    }

    #[test]
    fn test_sample_single_repeated() {
        use rand::distributions::uniform::{SampleUniform, UniformSampler};
        let mut rng = StdRng::seed_from_u64(42);
        // -(2**256 - 1)
        let lower = Arbi::from_str_radix(
            "-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        // 2**256 - 1
        let upper = Arbi::from_str_radix(
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let mid = 0;
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..(i16::MAX >> 1) {
            let arbi = <Arbi as SampleUniform>::Sampler::sample_single(
                &lower, &upper, &mut rng,
            );
            assert!(arbi >= lower && arbi < upper);
            if arbi > mid {
                num_above += 1;
            } else if arbi < mid {
                num_below += 1;
            }
        }
        let ratio = num_above as f64 / num_below as f64;
        assert!(0.95 < ratio && ratio < 1.05);
    }

    #[test]
    fn test_uniform_small() {
        let mut rng = StdRng::seed_from_u64(42);

        let lower = Arbi::from(1);
        let upper = Arbi::from(4);

        let uniform = Uniform::new(&lower, &upper);
        let mut values_sampled = std::collections::HashSet::new();

        for _ in 0..5000 {
            let arbi = uniform.sample(&mut rng);
            assert!(arbi >= lower && arbi < upper);
            values_sampled.insert(arbi.wrapping_to_i32());
        }

        assert_eq!(values_sampled.len(), 3);
        assert!(values_sampled.contains(&1));
        assert!(values_sampled.contains(&2));
        assert!(values_sampled.contains(&3));
    }

    #[test]
    fn test_uniform_inclusive_small() {
        let mut rng = StdRng::seed_from_u64(42);

        let lower = Arbi::from(1);
        let upper = Arbi::from(3);

        let uniform = Uniform::new_inclusive(&lower, &upper);
        let mut values_sampled = std::collections::HashSet::new();

        for _ in 0..5000 {
            let arbi = uniform.sample(&mut rng);
            assert!(arbi >= lower && arbi <= upper);
            values_sampled.insert(arbi.wrapping_to_i32());
        }

        assert_eq!(values_sampled.len(), 3);
        assert!(values_sampled.contains(&1));
        assert!(values_sampled.contains(&2));
        assert!(values_sampled.contains(&3));
    }
}
