/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};

impl Arbi {
    /// Increment this integer in-place by one.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut x = Arbi::from(987654321);
    /// x.incr();
    /// assert_eq!(x, 987654322);
    /// ```
    pub fn incr(&mut self) -> &mut Self {
        if self.neg {
            Self::decrement_abs(self);
            if self.size() == 0 {
                self.neg = false;
            }
        } else {
            Self::increment_abs(self);
        }
        self
    }

    /// Decrement this integer in-place by one.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut x = Arbi::from(987654321);
    /// x.decr();
    /// assert_eq!(x, 987654320);
    pub fn decr(&mut self) -> &mut Self {
        if self.neg {
            Self::increment_abs(self);
        } else if self.size() == 0 {
            Self::increment_abs(self);
            self.neg = true;
        } else {
            Self::decrement_abs(self);
        }
        self
    }

    /// Increment the absolute value of the number.
    fn increment_abs(&mut self) {
        Self::increment_abs_(self);
    }

    /// Decrement the absolute value of the number.
    fn decrement_abs(&mut self) {
        Self::decrement_abs_(self);
    }

    fn increment_abs_(x: &mut Self) {
        if x.size() == 0 || x.vec[x.size() - 1] == Digit::MAX {
            x.vec.reserve(1);
        }

        if x.size() == 0 {
            x.vec.resize(1, 0);
            x.vec[0] = 1;
            return;
        }

        let mut i: usize = 0;
        let mut carry: bool = true;

        while carry && i < x.size() {
            if x.vec[i] == Digit::MAX {
                x.vec[i] = 0;
            } else {
                x.vec[i] += 1;
                carry = false;
            }
            i += 1;
        }

        if carry {
            x.vec.push(1);
        }
    }

    fn decrement_abs_(x: &mut Self) {
        if x.size() == 0 {
            x.vec.clear();
            x.neg = false;
            return;
        }

        let mut i: usize = 0;
        let mut borrow: bool = true;

        while borrow && i < x.size() {
            if x.vec[i] == 0 {
                x.vec[i] = Digit::MAX;
            } else {
                x.vec[i] -= 1;
                borrow = false;
            }
            i += 1;
        }

        x.trim();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{DDigit, QDigit, SDDigit, SQDigit};

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();

        let die_p = get_uniform_die(
            Digit::MAX as DDigit - 100,
            Digit::MAX as DDigit + 100,
        );
        let die_z = get_uniform_die(-100, 100);
        let die_n = get_uniform_die(
            -(Digit::MAX as SDDigit) - 100,
            -(Digit::MAX as SDDigit) + 100,
        );

        for i in (i16::MIN + 1)..i16::MAX {
            let mut r: Arbi;

            let mut rp = die_p.sample(&mut rng);
            let mut rz = die_z.sample(&mut rng);
            let mut rn = die_n.sample(&mut rng);

            r = Arbi::from(rp);
            r.incr();
            rp += 1;
            assert_eq!(r, rp);
            r.decr().decr();
            rp -= 2;
            assert_eq!(r, rp);

            r = Arbi::from(rz);
            r.incr();
            rz += 1;
            assert_eq!(r, rz);
            r.decr().decr();
            rz -= 2;
            assert_eq!(r, rz);

            r = Arbi::from(rn);
            r.incr();
            rn += 1;
            assert_eq!(r, rn);
            r.decr().decr();
            rn -= 2;
            assert_eq!(r, rn);

            let mut j = i;
            r = Arbi::from(j);
            r.incr();
            j += 1;
            assert_eq!(r, j);
            r.decr().decr();
            j -= 2;
            assert_eq!(r, j);
        }
    }

    #[test]
    fn test_around_zero() {
        let mut arbi = Arbi::zero();
        arbi.incr();
        assert_eq!(arbi, 1);

        arbi.incr();
        assert_eq!(arbi, 2);

        arbi.decr();
        assert_eq!(arbi, 1);

        arbi.decr();
        assert_eq!(arbi, 0);

        arbi.decr();
        assert_eq!(arbi, -1);

        arbi.decr();
        assert_eq!(arbi, -2);

        arbi.incr().incr();
        assert_eq!(arbi, 0);

        arbi.incr();
        assert_eq!(arbi, 1);
    }

    #[test]
    fn test_increment_abs_around_digit_type_boundaries() {
        let mut digit_max = Arbi::from(Digit::MAX);
        digit_max.increment_abs();
        assert_eq!(digit_max, Digit::MAX as DDigit + 1);

        let mut ddigit_max = Arbi::from(DDigit::MAX);
        ddigit_max.increment_abs();
        assert_eq!(ddigit_max, DDigit::MAX as QDigit + 1);

        let mut minus_digit_max = Arbi::from(-(Digit::MAX as SDDigit));
        minus_digit_max.increment_abs();
        assert_eq!(minus_digit_max, -(Digit::MAX as SDDigit) - 1);

        let mut minus_ddigit_max = Arbi::from(-(DDigit::MAX as SQDigit));
        minus_ddigit_max.increment_abs();
        assert_eq!(minus_ddigit_max, -(DDigit::MAX as SQDigit) - 1);
    }

    #[test]
    fn test_decrement_abs_around_digit_type_boundaries() {
        // 2 digits down to 1
        let mut digit_max = Arbi::from(Digit::MAX as DDigit + 1);
        assert_eq!(digit_max.size(), 2);
        digit_max.decrement_abs();
        assert_eq!(digit_max, Digit::MAX);
        assert_eq!(digit_max.size(), 1);

        // 3 digits down to 2
        let mut ddigit_max = Arbi::from(DDigit::MAX as QDigit + 1);
        assert_eq!(ddigit_max.size(), 3);
        ddigit_max.decrement_abs();
        assert_eq!(ddigit_max, DDigit::MAX);
        assert_eq!(ddigit_max.size(), 2);

        // 2 digits down to 1
        let mut minus_digit_max = Arbi::from(-(Digit::MAX as SDDigit) - 1);
        assert_eq!(minus_digit_max.size(), 2);
        minus_digit_max.decrement_abs();
        assert_eq!(minus_digit_max, -(Digit::MAX as SDDigit));
        assert_eq!(minus_digit_max.size(), 1);

        // 3 digits down to 2
        let mut minus_ddigit_max = Arbi::from(-(DDigit::MAX as SQDigit) - 1);
        assert_eq!(minus_ddigit_max.size(), 3);
        minus_ddigit_max.decrement_abs();
        assert_eq!(minus_ddigit_max, -(DDigit::MAX as SQDigit));
        assert_eq!(minus_ddigit_max.size(), 2);
    }
}
