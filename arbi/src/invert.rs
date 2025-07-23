/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

impl Arbi {
    /// Return the inverse of `self` modulo `modulus`, if it exists. Otherwise,
    /// return `None`.
    ///
    /// Mathematically, if the inverse exists, the return value, \\( r \\),
    /// will be such that \\( 0 \leq r \lt |\text{modulus}| \\) (\\( 0 \\)
    /// only if \\( |\text{modulus}| = 1 \\)).
    ///
    /// # Panic
    /// Panics if `modulus` is zero.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// let (a, ma) = (Arbi::from(3), Arbi::from(-3));
    /// let (b, mb) = (Arbi::from(11), Arbi::from(-11));
    ///
    /// let i = a.invert_ref(&b).unwrap();
    /// assert_eq!(i, 4);
    ///
    /// let i = ma.invert_ref(&b).unwrap();
    /// assert_eq!(i, 7);
    ///
    /// let i = a.invert_ref(&mb).unwrap();
    /// assert_eq!(i, 4);
    ///
    /// let i = ma.invert_ref(&mb).unwrap();
    /// assert_eq!(i, 7);
    ///
    /// assert_eq!(a.invert_ref(&Arbi::one()).unwrap(), 0);
    /// assert_eq!(a.invert_ref(&Arbi::neg_one()).unwrap(), 0);
    ///
    /// assert_eq!(Arbi::zero().invert_ref(&a), None);
    /// assert_eq!(Arbi::zero().invert_ref(&ma), None);
    /// ```
    ///
    /// Panics if `modulus` is zero:
    /// ```should_panic
    /// use arbi::Arbi;
    /// Arbi::from(7).invert_ref(&Arbi::zero());
    /// ```
    pub fn invert_ref(&self, modulus: &Self) -> Option<Self> {
        assert!(!modulus.is_zero(), "modulus cannot be zero");
        if modulus.size() == 1 && modulus.vec[0] == 1 {
            // Modulus is -1 or 1
            return Some(Self::zero());
        }
        // TODO: analyze how we can minimize allocations
        /* Assumes m > 1 */
        let (mut q, mut r) = (Arbi::zero(), Arbi::zero());
        let mut a = self.clone();
        let mut s = Self::one();
        let mut t = Self::zero();
        let mut m = modulus.clone();
        while !m.is_zero() {
            // Floor division, treating m as positive
            Self::fddivide(&mut q, &mut r, &a.vec, &m.vec, a.signum(), 1);
            a = m;
            m = core::mem::take(&mut r);
            let nt = s - core::mem::take(&mut q) * &t;
            s = t;
            t = nt;
        }
        if a != 1 {
            // Inverse does not exist
            return None;
        }
        /* At this point, s is an inverse to self modulo |modulus| such that
         * |s| < |modulus|. Now adjust for potentially negative modulus
         */
        // NOTE: If we are happy with 0 <= |r| < |modulus|, just return this:
        // match (modulus.is_negative(), s.is_negative()) {
        //     (true, false) | (false, true) => Some(s + modulus),
        //     _ => Some(s),
        // }
        // However, we want 0 <= r < |modulus|.
        let mut x = s % modulus;
        if x.is_negative() {
            if modulus.is_negative() {
                x -= modulus;
            } else {
                x += modulus;
            }
        }
        Some(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{SDDigit, SDigit, SQDigit};

    pub fn gcdext(a: i128, b: i128) -> (i128, i128, i128) {
        if a == 0 && b == 0 {
            return (0, 0, 0);
        }
        let (mut old_r, mut r) = (a, b);
        let (mut old_s, mut s) = (1, 0);
        let (mut old_t, mut t) = (0, 1);
        while r != 0 {
            let quotient = old_r / r;
            old_r = old_r - quotient * r;
            std::mem::swap(&mut old_r, &mut r);
            old_s = old_s - quotient * s;
            std::mem::swap(&mut old_s, &mut s);
            old_t = old_t - quotient * t;
            std::mem::swap(&mut old_t, &mut t);
        }
        if old_r < 0 {
            (-old_r, -old_s, -old_t)
        } else {
            (old_r, old_s, old_t)
        }
    }

    pub fn modinv(a: i128, m: i128) -> Option<i128> {
        if m == 0 {
            panic!("modulus cannot be zero");
        }
        let (gcd, s, _) = gcdext(a, m);
        if gcd != 1 {
            return None;
        }
        // Ensure result is in range [0, abs(m))
        let abs_m = m.abs();
        let mut result = s % abs_m;
        if result < 0 {
            result += abs_m;
        }
        Some(result)
    }

    #[test]
    #[should_panic = "modulus cannot be zero"]
    fn zero_modulus_panics() {
        Arbi::from(1).invert_ref(&Arbi::from(0));
    }

    #[test]
    #[should_panic = "modulus cannot be zero"]
    fn zero_modulus_panics_reference() {
        modinv(1, 0);
    }

    #[test]
    fn one_modulus() {
        assert_eq!(Arbi::from(12345).invert_ref(&Arbi::one()).unwrap(), 0);
        assert_eq!(Arbi::from(-12345).invert_ref(&Arbi::one()).unwrap(), 0);
        assert_eq!(Arbi::from(12345).invert_ref(&Arbi::neg_one()).unwrap(), 0);
        assert_eq!(Arbi::from(-12345).invert_ref(&Arbi::neg_one()).unwrap(), 0);
        assert_eq!(Arbi::zero().invert_ref(&Arbi::one()).unwrap(), 0);
        assert_eq!(Arbi::zero().invert_ref(&Arbi::neg_one()).unwrap(), 0);
    }

    #[test]
    fn one_modulus_reference() {
        assert_eq!(modinv(12345, 1).unwrap(), 0);
        assert_eq!(modinv(-12345, 1).unwrap(), 0);
        assert_eq!(modinv(12345, -1).unwrap(), 0);
        assert_eq!(modinv(-12345, -1).unwrap(), 0);
        assert_eq!(modinv(0, 1).unwrap(), 0);
        assert_eq!(modinv(0, -1).unwrap(), 0);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let small = get_uniform_die(i8::MIN, i8::MAX);
        let sd = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let sdd = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let sqd = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        let num_samples = 5000 as usize;
        let mut samples: Vec<(i128, i128)> =
            Vec::with_capacity(num_samples * 3);

        for _ in 0..num_samples {
            // (i32, i32)
            let a = sd.sample(&mut rng) as i128;
            let m = sd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i64, i64)
            let a = sdd.sample(&mut rng) as i128;
            let m = sdd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i128, i128)
            let a = sqd.sample(&mut rng) as i128;
            let m = sqd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i32, i128)
            let a = sd.sample(&mut rng) as i128;
            let m = sqd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i128, i32)
            let a = sqd.sample(&mut rng) as i128;
            let m = sd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i32, i64)
            let a = sd.sample(&mut rng) as i128;
            let m = sdd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i8, i8)
            let a = small.sample(&mut rng) as i128;
            let m = small.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i8, i64)
            let a = small.sample(&mut rng) as i128;
            let m = sdd.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
            // (i64, i8)
            let a = sdd.sample(&mut rng) as i128;
            let m = small.sample(&mut rng) as i128;
            if m != 0 {
                samples.push((a, m))
            };
        }

        for (a, m) in samples {
            let arbi_a = Arbi::from(a);
            let arbi_m = Arbi::from(m);
            assert_eq!(
                arbi_a.invert_ref(&arbi_m).unwrap_or(Arbi::neg_one()),
                modinv(a, m).unwrap_or(-1)
            );
        }
    }
}
