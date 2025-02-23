/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::uints::UnsignedUtilities;
use crate::{Arbi, BitCount, Digit};
use rand::Rng;

/// Trait for generating random `Arbi` integers.
pub trait RandomArbi {
    /// Generate a random `Arbi` integer in the closed interval
    /// \\( [0, 2^{\text{bits}} - 1] \\).
    ///
    /// # Panic
    /// Panics if `Vec`'s maximum capacity is exceeded, i.e. `bits` exceeds
    /// [`Arbi::MAX_BITS`] (or if the allocator reports allocation failure).
    fn gen_uarbi(&mut self, bits: BitCount) -> Arbi;

    /// Generate a random `Arbi` integer in the closed interval
    /// \\( [-(2^{\text{bits}} - 1), \\; 2^{\text{bits}} - 1] \\).
    ///
    /// # Panic
    /// Panics if `Vec`'s maximum capacity is exceeded, i.e. `bits` exceeds
    /// [`Arbi::MAX_BITS`] (or if the allocator reports allocation failure).
    fn gen_iarbi(&mut self, bits: BitCount) -> Arbi;

    /// Generate a random `Arbi` integer in the half-open interval
    /// \\( [\text{lower_incl}, \\; \text{upper_excl})\\).
    ///
    /// # Panic
    /// Panics if `lower_incl >= upper_excl`.
    fn gen_arbi_range(&mut self, lower_incl: &Arbi, upper_excl: &Arbi) -> Arbi;

    /// Generate a random `Arbi` integer in the half-open interval
    /// \\( [0, \\; \text{upper_excl})\\).
    ///
    /// # Panic
    /// Panics if `upper_excl` is zero.
    fn gen_uarbi_under(&mut self, upper_excl: &Arbi) -> Arbi;
}

// https://docs.rs/rand/latest/rand/trait.Rng.html#generic-usage
impl<T: Rng + ?Sized> RandomArbi for T {
    fn gen_uarbi(&mut self, bits: BitCount) -> Arbi {
        let mut arbi = Arbi::zero();
        assign_random_uarbi(self, &mut arbi, bits);
        arbi
    }

    fn gen_iarbi(&mut self, bits: BitCount) -> Arbi {
        // Suppose gen_uarbi(bits) gives each integer in [0, 2^{bits} - 1] a
        // probability of 1/2^{bits}.
        //
        // If the integer is not zero, that is, it is positive, suppose we
        // negate it with probability 0.5. Then the probability of an integer in
        // [1, 2^{bits} - 1] is 0.5/2^{bits} and symmetrically, the probability
        // of an integer in [-(2^{bits} - 1), -1] is 0.5/2^{bits}.
        //
        // If the integer is zero, without any adjustment, the probability would
        // be 1/2^{bits} > 0.5/2^{bits}. Consequently, an adjustment is needed
        // to ensure zero is not more likely than each possible positive or
        // negative value.
        let mut arbi = self.gen_uarbi(bits);
        loop {
            if !arbi.is_zero() {
                arbi.neg = self.gen::<bool>();
                return arbi;
            } else if self.gen::<bool>() {
                return arbi;
            } else {
                assign_random_uarbi(self, &mut arbi, bits);
            }
        }
    }

    fn gen_arbi_range(&mut self, lower_incl: &Arbi, upper_excl: &Arbi) -> Arbi {
        if lower_incl >= upper_excl {
            panic!("void range");
        }
        if lower_incl.is_zero() {
            return self.gen_uarbi_under(upper_excl);
        }
        let diff = upper_excl - lower_incl;
        lower_incl + self.gen_uarbi_under(&diff)
    }

    fn gen_uarbi_under(&mut self, upper_excl: &Arbi) -> Arbi {
        if upper_excl.is_zero() {
            panic!("void range")
        }
        let bits = upper_excl.size_bits();
        let mut random_arbi = self.gen_uarbi(bits);
        while upper_excl <= &random_arbi {
            assign_random_uarbi(self, &mut random_arbi, bits);
        }
        random_arbi
    }
}

fn assign_random_uarbi<T: Rng + ?Sized>(
    rng: &mut T,
    arbi: &mut Arbi,
    bits: BitCount,
) {
    let n_digits_ = BitCount::div_ceil_(bits, Digit::BITS as BitCount);
    let n_digits: usize = n_digits_.try_into().unwrap_or(usize::MAX);
    arbi.vec.resize(n_digits, 0);
    rng.fill(&mut arbi.vec[..]);
    let remaining = bits % Digit::BITS as BitCount;
    if remaining != 0 {
        if let Some(last_digit) = arbi.vec.last_mut() {
            let mask = Digit::MAX >> (Digit::BITS as BitCount - remaining);
            *last_digit &= mask;
        }
    }
    arbi.neg = false;
    arbi.trim();
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::mock::StepRng;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    #[test]
    #[should_panic(expected = "void range")]
    fn test_gen_uarbi_under_where_upper_is_zero() {
        let mut rng = StepRng::new(42, 0);
        let upper_excl = Arbi::zero();
        let _ = rng.gen_uarbi_under(&upper_excl);
    }

    #[test]
    #[should_panic(expected = "void range")]
    fn test_gen_arbi_range_where_range_is_invalid() {
        let mut rng = StepRng::new(42, 0);
        let lower_incl = Arbi::zero();
        let upper_excl = Arbi::from(-1000);
        let _ = rng.gen_arbi_range(&lower_incl, &upper_excl);
    }

    #[test]
    #[should_panic(expected = "capacity overflow")]
    fn test_gen_uarbi_bits_panics_if_max_bits_exceeded() {
        let mut rng = StepRng::new(42, 1);
        let _ = rng.gen_uarbi(Arbi::MAX_BITS + 1);
    }

    #[test]
    #[should_panic(expected = "capacity overflow")]
    fn test_gen_iarbi_bits_panics_if_max_bits_exceeded() {
        let mut rng = StepRng::new(42, 1);
        let _ = rng.gen_iarbi(Arbi::MAX_BITS + 1);
    }

    #[test]
    fn test_gen_uarbi_is_zero_if_bits_is_zero() {
        let mut rng = StepRng::new(42, 1);
        let a = rng.gen_uarbi(0);
        assert_eq!(a, 0);
    }

    #[test]
    fn test_gen_iarbi_is_zero_if_bits_is_zero() {
        let mut rng = StepRng::new(42, 1);
        let a = rng.gen_iarbi(0);
        assert_eq!(a, 0);
    }

    #[test]
    fn test_gen_arbi_range_is_zero_for_0_to_1() {
        let mut rng = StepRng::new(42, 1);
        let a = rng.gen_arbi_range(&Arbi::ZERO, &Arbi::from(1));
        assert_eq!(a, 0);
    }

    #[test]
    fn test_gen_uarbi_under_is_zero_for_1_upperbound() {
        let mut rng = StepRng::new(42, 1);
        let a = rng.gen_uarbi_under(&Arbi::from(1));
        assert_eq!(a, 0);
    }

    #[test]
    fn test_gen_uarbi_repeated() {
        let mut rng = StdRng::seed_from_u64(42);
        let mid = Arbi::from_str_radix(
            "3138550867693340381917894711603833208051177722232017256447",
            10,
        )
        .unwrap();
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..i16::MAX {
            let arbi = rng.gen_uarbi(192);
            assert!(arbi >= 0);
            assert!(arbi.size_bits() <= 192);
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
    fn test_gen_iarbi_repeated() {
        let mut rng = StdRng::seed_from_u64(42);
        let mid = 0;
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..i16::MAX {
            let arbi = rng.gen_iarbi(256);
            assert!(arbi.size_bits() <= 256);
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
    fn test_gen_uarbi_under_repeated() {
        let mut rng = StdRng::seed_from_u64(42);
        let upper_excl = Arbi::from_str_radix(
            // 2**256 - 1
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            16,
        )
        .unwrap();
        let mid = upper_excl.clone() >> 1;
        let mut num_above = 0;
        let mut num_below = 0;
        for _ in 0..i16::MAX {
            let arbi = rng.gen_uarbi_under(&upper_excl);
            assert!(arbi >= 0 && arbi < upper_excl);
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
    fn test_gen_arbi_range_repeated() {
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
        for _ in 0..i16::MAX {
            let arbi = rng.gen_arbi_range(&lower, &upper);
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
}
