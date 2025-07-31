/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, DDigit, Digit};

impl Arbi {
    //  A nonnegative integer with n digits in base-B >= 2 has maximum value
    //  B^{n} - 1.
    //  ==> integers a, b, c have maximum values B^{n_a} - 1, ..., B^{n_c} - 1.
    //  ==>
    //      a + b + c <= (B^{n_a} - 1) + (B^{n_b} - 1) + (B^{n_c} - 1)
    //                 = B^{n_a} + B^{n_b} + B^{n_c} - 3
    //  Define N = max{n_a, n_b, n_c} so that B^N >= B^{n_a}, B^{n_b}, B^{n_c}.
    //  ==>
    //      a + b + c <= B^{N} + B^{N} + B^{N} - 3
    //                 = 3B^{N} - 3
    //  We want to show that an N + 1 digit base-B integer can hold the sum:
    //      3B^{N} - 3 <= B^{N + 1} - 1 = B x B^{N} - 1
    //  <==>
    //      -3 <= B x B^{N} - 1 - 3B^{N}
    //  <==>
    //      -3 <= (B - 3)B^{N} - 1
    //  <==>
    //      -2 <= (B - 3)B^{N}
    //  But
    //      B >= 2 ==> (B - 3) >= -1 ==> (B - 3)B^{N} >= -B^{N} >= -2
    //      (for B >= 2).
    //  Thus, B^{N + 1} - 1 is an upper bound for the sum a + b + c.
    //  The maximum number of digits needed to represent a + b + c is therefore
    //      N + 1 = max{n_a, n_b, n_c} + 1.
    /// \\( self = |a| + |b| + |c| \\).
    pub(crate) fn add3_abs_assign(&mut self, a: &Arbi, b: &Arbi, c: &Arbi) {
        let max_size = a.size().max(b.size()).max(c.size());
        self.vec.resize(max_size + 1, 0); // see proof above
        let mut carry: Digit = 0;
        for i in 0..max_size {
            let mut sum: DDigit = carry as DDigit;
            carry = 0;
            if i < a.size() {
                sum += a.vec[i] as DDigit;
            }
            if i < b.size() {
                sum += b.vec[i] as DDigit;
            }
            if i < c.size() {
                sum += c.vec[i] as DDigit;
            }
            if sum >= Arbi::BASE {
                carry = (sum >> Digit::BITS) as Digit;
                sum -= Arbi::BASE;
            }
            self.vec[i] = sum as Digit;
        }
        self.vec[max_size] = carry;
        self.trim();
        self.neg = false;
    }

    /// \\( self = |self| - (|a| + |b|) \\), assuming |self| >= (|a| + |b|).
    pub(crate) fn sub_sum_of_abs_gt(&mut self, a: &Arbi, b: &Arbi) {
        let mut carry: Digit = 0;
        let mut borrow: Digit = 0;
        for i in 0..self.size() {
            // Add
            let mut sum: DDigit = carry as DDigit;
            carry = 0;
            if i < a.size() {
                sum += a.vec[i] as DDigit;
            }
            if i < b.size() {
                sum += b.vec[i] as DDigit;
            }
            if sum >= Arbi::BASE {
                carry = (sum >> Digit::BITS) as Digit;
                sum -= Arbi::BASE;
            }
            // Sub
            let (digit, borrow_p) =
                self.vec[i].overflowing_sub(sum as Digit + borrow);
            self.vec[i] = digit;
            borrow = Digit::from(borrow_p);
        }
        self.trim();
        self.neg = false;
    }
}

#[cfg(test)]
mod test_add3_abs_assign {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, QDigit};

    #[test]
    fn test_sum_gt_arbi_base_branch() {
        let mut s = Arbi::zero();
        let a = 9368850493200048722_u64;
        let b = 11334117686971261073_u64;
        let c = 9795558189060012567_u64;
        s.add3_abs_assign(&Arbi::from(a), &Arbi::from(b), &Arbi::from(c));
        assert_eq!(s, QDigit::from(a) + QDigit::from(b) + QDigit::from(c));
    }

    #[test]
    fn test_nonzero_carry_after_loop() {
        let mut s = Arbi::zero();
        let a = 17384971691622762845_u64;
        let b = 13975311186207392826_u64;
        let c = 12301324174353418444_u64;
        s.add3_abs_assign(&Arbi::from(a), &Arbi::from(b), &Arbi::from(c));
        assert_eq!(s, QDigit::from(a) + QDigit::from(b) + QDigit::from(c));
    }

    #[test]
    fn test_zero_carry_after_loop() {
        let mut s = Arbi::zero();
        let a = 1743738137480021943_u64;
        let b = 1619148075948679532_u64;
        let c = 2567961127114686782_u64;
        s.add3_abs_assign(&Arbi::from(a), &Arbi::from(b), &Arbi::from(c));
        assert_eq!(s, QDigit::from(a) + QDigit::from(b) + QDigit::from(c));
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(DDigit::MIN, DDigit::MAX);
        let mut s = Arbi::zero();
        for _ in 0..i16::MAX {
            let a = die.sample(&mut rng);
            let b = die.sample(&mut rng);
            let c = die.sample(&mut rng);
            s.add3_abs_assign(&Arbi::from(a), &Arbi::from(b), &Arbi::from(c));
            assert_eq!(s, QDigit::from(a) + QDigit::from(b) + QDigit::from(c));
        }
    }
}

#[cfg(test)]
mod test_sub_sum_of_abs_gt {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, QDigit};

    #[test]
    fn test_sum_gt_arbi_base_branch() {
        let s = 13005330410001137702_u64;
        let a = 9033044601729108003_u64;
        let b = 1986771123253152281_u64;
        let mut slf = Arbi::from(s);
        slf.sub_sum_of_abs_gt(&Arbi::from(a), &Arbi::from(b));
        assert_eq!(slf, QDigit::from(s) - (QDigit::from(a) + QDigit::from(b)));
    }

    #[test]
    fn test_true_borrow_p() {
        let s = 9416850955672696351_u64;
        let a = 769802824207354958_u64;
        let b = 3480730557869871236_u64;
        let mut slf = Arbi::from(s);
        slf.sub_sum_of_abs_gt(&Arbi::from(a), &Arbi::from(b));
        assert_eq!(slf, QDigit::from(s) - (QDigit::from(a) + QDigit::from(b)));
    }

    #[test]
    fn test_false_borrow_p() {
        let s = 14351946877333955861_u64;
        let a = 7257282171651561537_u64;
        let b = 1329917829030286033_u64;
        let mut slf = Arbi::from(s);
        slf.sub_sum_of_abs_gt(&Arbi::from(a), &Arbi::from(b));
        assert_eq!(slf, QDigit::from(s) - (QDigit::from(a) + QDigit::from(b)));
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(DDigit::MIN, DDigit::MAX);
        for _ in 0..i16::MAX {
            let s = die.sample(&mut rng);
            let a = die.sample(&mut rng);
            let b = die.sample(&mut rng);
            if QDigit::from(s) < QDigit::from(a) + QDigit::from(b) {
                continue;
            }
            let mut slf = Arbi::from(s);
            slf.sub_sum_of_abs_gt(&Arbi::from(a), &Arbi::from(b));
            assert_eq!(
                slf,
                QDigit::from(s) - (QDigit::from(a) + QDigit::from(b))
            );
        }
    }
}
