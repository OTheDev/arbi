/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

#![cfg(feature = "rand")]

use crate::uints::UnsignedUtilities;
use crate::{Arbi, BitCount, Digit};
use rand::Rng;

/// Trait for generating random `Arbi` integers.
pub trait RandomArbi {
    /// Generate a random `Arbi` integer in the interval
    /// \\( [0, 2^{\text{bits}} - 1] \\).
    fn gen_uarbi(&mut self, bits: BitCount) -> Arbi;

    /// Generate a random `Arbi` integer in the interval
    /// \\( [-(2^{\text{bits}} - 1), \\; 2^{\text{bits}} - 1] \\).
    fn gen_iarbi(&mut self, bits: BitCount) -> Arbi;

    /// Generate a random `Arbi` integer in the half-open interval
    /// \\( [\text{lower_incl}, \\; \text{upper_excl})\\).
    ///
    /// # Panic
    /// This function panics if `lower_incl >= upper_excl`.
    fn gen_arbi_range(&mut self, lower_incl: &Arbi, upper_excl: &Arbi) -> Arbi;
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
        // Commented out if using only RngCore
        // loop {
        //     let mut arbi = self.gen_uarbi(bits);
        //     if !arbi.is_zero() {
        //         arbi.neg = self.next_u32() % 2 == 0;
        //         return arbi;
        //     } else if self.next_u32() % 2 == 0 {
        //         return arbi;
        //     }
        // }
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
            return gen_uarbi_under(self, upper_excl);
        }
        let diff = upper_excl - lower_incl;
        lower_incl + gen_uarbi_under(self, &diff)
    }
}

fn assign_random_uarbi<T: Rng + ?Sized>(
    rng: &mut T,
    arbi: &mut Arbi,
    bits: BitCount,
) {
    let n_digits_ = BitCount::div_ceil_(bits, Digit::BITS as BitCount);
    let n_digits: usize = n_digits_.try_into().unwrap_or(usize::MAX);
    // Commented out if using only RngCore
    // let mut vec = Vec::with_capacity(n_digits);
    // for _ in 0..n_digits {
    //     vec.push(self.next_u32());
    // }
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

#[allow(dead_code)]
/// Return a random `Arbi` integer in [0, upper_excl).
///
/// # Panic
/// Panics if `upper_excl` is zero.
fn gen_uarbi_under<T: Rng + ?Sized>(rng: &mut T, upper_excl: &Arbi) -> Arbi {
    if upper_excl.is_zero() {
        panic!("void range")
    }
    let bits = upper_excl.size_bits();
    let mut random_arbi = rng.gen_uarbi(bits);
    while upper_excl <= &random_arbi {
        assign_random_uarbi(rng, &mut random_arbi, bits);
    }
    random_arbi
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::mock::StepRng;

    #[test]
    #[should_panic(expected = "void range")]
    fn test_gen_uarbi_under_where_upper_is_zero() {
        let mut rng = StepRng::new(42, 0);
        let upper_excl = Arbi::zero();
        let _ = gen_uarbi_under(&mut rng, &upper_excl);
    }

    #[test]
    #[should_panic(expected = "void range")]
    fn test_gen_arbi_range_where_range_is_invalid() {
        let mut rng = StepRng::new(42, 0);
        let lower_incl = Arbi::zero();
        let upper_excl = Arbi::from(-1000);
        let _ = rng.gen_arbi_range(&lower_incl, &upper_excl);
    }
}
