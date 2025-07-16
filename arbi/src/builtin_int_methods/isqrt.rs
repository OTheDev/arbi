/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;
use crate::Assign;

impl Arbi {
    /// Returns the square root of the number, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt(mut self) -> Self {
        self.isqrt_mut();
        self
    }

    /// Returns the square root of the number, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt_ref(&self) -> Self {
        self.clone().isqrt()
    }

    /// Replaces `self` with its square root, rounded down.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn isqrt_mut(&mut self) {
        if self.is_negative() {
            panic!("argument of integer square root cannot be negative");
        }

        if self.is_zero() {
            return;
        }

        #[cfg(not(test))]
        {
            use crate::uints::UnsignedUtilities;
            // Fast path for small integers
            if let Some(val) = self.checked_to_u128() {
                // If self fits in a u128, use binary search (no memory
                // allocation). This should be tested separately.
                // Skipped during tests to ensure the general algorithm is
                // exercised.
                self.assign(val.isqrt_());
                return;
            }
        }

        // Algorithm 1.13 SqrtInt from Brent and Zimmerman (2010)
        // Input: an integer m >= 1
        // Output: s = floor(m^(1/2))
        let mut s = Arbi::new();
        let mut t = Arbi::new();

        // 1. u <- m (any value u ≥ ⌊m^(1/2)⌋ works). We follow parentheses
        let mut u = Arbi::one() << ((self.size_bits() + 1) >> 1);

        // 2. repeat
        loop {
            // 3. s <- u
            s.assign(&u);

            // 4. t <- s + floor(m/s)
            t.assign(&*self);
            t /= &s; // floor(m/s)
            t += &s; // s + floor(m/s)

            // 5. u <- floor(t/2)
            u.assign(&t);
            u >>= 1; // Divide by 2 (floor division for positive numbers)

            // 6. until u >= s
            if u >= s {
                break;
            }
        }

        // 7. return s
        self.assign(&s);
    }
}

#[cfg(test)]
mod tests {
    use crate::uints::UnsignedUtilities;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit, QDigit};

    #[test]
    fn test_isqrt_basic() {
        for i in 0..11000u32 {
            assert_eq!(Arbi::from(i).isqrt(), i.isqrt_());
        }
    }

    #[test]
    #[should_panic = "argument of integer square root cannot be negative"]
    fn test_isqrt_negative() {
        let val = Arbi::from(-1);
        val.isqrt();
    }

    #[test]
    fn test_digit_boundaries() {
        let dmax = Digit::MAX;
        let dmaxp1 = dmax as DDigit + 1;
        let ddmax = DDigit::MAX;
        let ddmaxp1 = ddmax as QDigit + 1;

        assert_eq!(Arbi::from(dmax).isqrt(), dmax.isqrt_());
        assert_eq!(Arbi::from(dmaxp1).isqrt(), dmaxp1.isqrt_());
        assert_eq!(Arbi::from(ddmax).isqrt(), ddmax.isqrt_());
        assert_eq!(Arbi::from(ddmaxp1).isqrt(), ddmaxp1.isqrt_());
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_digit = get_uniform_die(Digit::MIN, Digit::MAX);
        let die_ddigit = get_uniform_die(Digit::MAX as DDigit + 1, DDigit::MAX);
        let die_qdigit =
            get_uniform_die(DDigit::MAX as QDigit + 1, QDigit::MAX);

        for _ in 0..i16::MAX {
            let r = die_digit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());

            let r = die_ddigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());

            let r = die_qdigit.sample(&mut rng);
            let a = Arbi::from(r);
            assert_eq!(a.isqrt(), r.isqrt_());
        }
    }

    #[test]
    fn test_large() {
        let cases = [
            (
                "765897785077764057608430480697850143361",
                27674858356959373200u128,
            ),
            (
                "766547856473138565884960566918156275607",
                27686600666624614822u128,
            ),
            (
                "999875546082047415934405945671979461267",
                31620808751232904162u128
            ),
            (
                "115792089237316195423570985008687907852589419931798687112530834793049593217025",
                340282366920938463463374607431768211455u128
            ),
        ];

        for case in cases {
            let mut n = Arbi::from_str_radix(case.0, 10).unwrap();
            n.isqrt_mut();

            assert_eq!(n, case.1);
        }
    }
}
