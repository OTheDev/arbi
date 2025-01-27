/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::util::view::ArbiLikeView;
use crate::{Arbi, Assign, Digit};

#[derive(Debug, Copy, Clone)]
pub enum BitwiseOp {
    And,
    Ior,
    Xor,
}

#[inline]
fn tcom_digit_of_neg_arg(digit: Digit, carry: &mut bool) -> Digit {
    let (digit, overflow) = (!digit).overflowing_add(*carry as Digit);
    *carry = overflow;
    digit
}

#[inline]
fn smag_digit_of_pos_res(
    x_digit: Digit,
    y_digit: Digit,
    op: BitwiseOp,
) -> Digit {
    match op {
        BitwiseOp::And => x_digit & y_digit,
        BitwiseOp::Ior => x_digit | y_digit,
        BitwiseOp::Xor => x_digit ^ y_digit,
    }
}

#[inline]
fn smag_digit_of_neg_res(
    x_digit: Digit,
    y_digit: Digit,
    op: BitwiseOp,
    carry: &mut bool,
) -> Digit {
    let (digit, overflow) = match op {
        BitwiseOp::And => {
            (!(x_digit & y_digit)).overflowing_add(*carry as Digit)
        }
        BitwiseOp::Ior => {
            (!(x_digit | y_digit)).overflowing_add(*carry as Digit)
        }
        BitwiseOp::Xor => {
            (!(x_digit ^ y_digit)).overflowing_add(*carry as Digit)
        }
    };
    *carry = overflow;
    digit
}

/*
(1) x_size >= y_size.
(2) Result is stored in self.
(3) Exactly one of x_vec, y_vec can be self.vec, but neither of them is
    perfectly acceptable too.
*/
macro_rules! bitwise_op_size_gte_impl {
    ($self:expr, $x_vec:expr, $y_vec:expr, $x_size:expr, $y_size:expr, $x_neg:expr, $y_neg:expr, $op:expr) => {{
        debug_assert!($x_vec.len() == $x_size);
        debug_assert!($y_vec.len() == $y_size);
        debug_assert!($x_size >= $y_size);
        let z_is_neg: bool = match $op {
            BitwiseOp::And => $x_neg & $y_neg,
            BitwiseOp::Ior => $x_neg | $y_neg,
            BitwiseOp::Xor => $x_neg ^ $y_neg,
        };
        let z_size: usize = match $op {
            BitwiseOp::And => {
                if $y_neg {
                    $x_size
                } else {
                    $y_size
                }
            }
            BitwiseOp::Ior => {
                if $y_neg {
                    $y_size
                } else {
                    $x_size
                }
            }
            BitwiseOp::Xor => $x_size,
        };
        $self.vec.resize(z_size + (z_is_neg as usize), 0);
        let carry = match ($x_neg, $y_neg) {
            (false, false) => {
                /* (x >= 0, y >= 0) ==> y bits are 00...0 in [$y_size, ...) */
                for j in 0..$y_size {
                    $self.vec[j] =
                        smag_digit_of_pos_res($x_vec[j], $y_vec[j], $op);
                }
                for j in $y_size..z_size {
                    $self.vec[j] = smag_digit_of_pos_res($x_vec[j], 0, $op);
                }
                false
            }
            (false, true) => {
                /* (x >= 0, y < 0) ==> y bits are 11...1 in [$y_size, ...) */
                let mut y_overflow = true;
                match z_is_neg {
                    true => {
                        let mut z_overflow = true;
                        for j in 0..$y_size {
                            let y_digit = tcom_digit_of_neg_arg(
                                $y_vec[j],
                                &mut y_overflow,
                            );
                            $self.vec[j] = smag_digit_of_neg_res(
                                $x_vec[j],
                                y_digit,
                                $op,
                                &mut z_overflow,
                            );
                        }
                        for j in $y_size..z_size {
                            $self.vec[j] = smag_digit_of_neg_res(
                                $x_vec[j],
                                Digit::MAX,
                                $op,
                                &mut z_overflow,
                            );
                        }
                        z_overflow
                    }
                    false => {
                        for j in 0..$y_size {
                            let y_digit = tcom_digit_of_neg_arg(
                                $y_vec[j],
                                &mut y_overflow,
                            );
                            $self.vec[j] =
                                smag_digit_of_pos_res($x_vec[j], y_digit, $op);
                        }
                        for j in $y_size..z_size {
                            $self.vec[j] = smag_digit_of_pos_res(
                                $x_vec[j],
                                Digit::MAX,
                                $op,
                            );
                        }
                        false
                    }
                }
            }
            (true, false) => {
                /* (x < 0, y >= 0) ==> y bits are 00...0 in [$y_size, ...) */
                let mut x_overflow = true;
                match z_is_neg {
                    true => {
                        let mut z_overflow = true;
                        for j in 0..$y_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            $self.vec[j] = smag_digit_of_neg_res(
                                x_digit,
                                $y_vec[j],
                                $op,
                                &mut z_overflow,
                            );
                        }
                        for j in $y_size..z_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            $self.vec[j] = smag_digit_of_neg_res(
                                x_digit,
                                0,
                                $op,
                                &mut z_overflow,
                            );
                        }
                        z_overflow
                    }
                    false => {
                        for j in 0..$y_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            $self.vec[j] =
                                smag_digit_of_pos_res(x_digit, $y_vec[j], $op);
                        }
                        /* No second loop needed.
                          And: since y >= 0, y_size applies.
                          Ior: result sign is $x_neg | $y_neg, so z_is_neg is
                               true.
                          Xor: result sign is $x_neg ^ $y_neg, so z_is_neg is
                               true.
                        */
                        false
                    }
                }
            }
            (true, true) => {
                /* (x < 0, y < 0) ==> y bits are 11...1 in [$y_size, ...) */
                let mut x_overflow = true;
                let mut y_overflow = true;
                match z_is_neg {
                    true => {
                        let mut z_overflow = true;
                        for j in 0..$y_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            let y_digit = tcom_digit_of_neg_arg(
                                $y_vec[j],
                                &mut y_overflow,
                            );
                            $self.vec[j] = smag_digit_of_neg_res(
                                x_digit,
                                y_digit,
                                $op,
                                &mut z_overflow,
                            );
                        }
                        for j in $y_size..z_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            $self.vec[j] = smag_digit_of_neg_res(
                                x_digit,
                                Digit::MAX,
                                $op,
                                &mut z_overflow,
                            );
                        }
                        z_overflow
                    }
                    false => {
                        for j in 0..$y_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            let y_digit = tcom_digit_of_neg_arg(
                                $y_vec[j],
                                &mut y_overflow,
                            );
                            $self.vec[j] =
                                smag_digit_of_pos_res(x_digit, y_digit, $op);
                        }
                        for j in $y_size..z_size {
                            let x_digit = tcom_digit_of_neg_arg(
                                $x_vec[j],
                                &mut x_overflow,
                            );
                            $self.vec[j] =
                                smag_digit_of_pos_res(x_digit, Digit::MAX, $op);
                        }
                        false
                    }
                }
            }
        };
        if carry {
            $self.vec[z_size] = 1;
        } else {
            $self.vec.truncate(z_size);
        }
        $self.neg = z_is_neg;
        $self.trim();
    }};
}

macro_rules! inplace_bitwise_op {
    ($self:expr, $other:expr, $op:expr) => {{
        let x_size: usize = $self.size();
        let y_size: usize = $other.size();
        if x_size >= y_size {
            if $other.is_zero() {
                if let BitwiseOp::And = $op {
                    $self.make_zero();
                }
                return;
            }
            bitwise_op_size_gte_impl!(
                $self, $self.vec, $other.vec, x_size, y_size, $self.neg,
                $other.neg, $op
            )
        } else {
            if $self.is_zero() {
                if let BitwiseOp::Ior | BitwiseOp::Xor = $op {
                    $self.assign($other);
                }
                return;
            }
            bitwise_op_size_gte_impl!(
                $self, $other.vec, $self.vec, y_size, x_size, $other.neg,
                $self.neg, $op
            )
        };
    }};
}

impl Arbi {
    pub(crate) fn inplace_bitwise_op(&mut self, other: &Arbi, op: BitwiseOp) {
        inplace_bitwise_op!(self, other, op);
    }

    pub(crate) fn assign_bitwise_operation(
        &mut self,
        x: &Arbi,
        y: &Arbi,
        op: BitwiseOp,
    ) {
        let (x, y, x_size, y_size): (&Arbi, &Arbi, usize, usize) =
            if x.size() < y.size() {
                (y, x, y.size(), x.size())
            } else {
                (x, y, x.size(), y.size())
            };
        if y_size == 0 {
            match op {
                BitwiseOp::And => self.make_zero(),
                _ => self.assign(x),
            }
            return;
        }
        bitwise_op_size_gte_impl!(
            self, x.vec, y.vec, x_size, y_size, x.neg, y.neg, op
        );
    }

    pub(crate) fn inplace_bitwise_op_with_arbi_like_view(
        &mut self,
        other: ArbiLikeView,
        op: BitwiseOp,
    ) {
        inplace_bitwise_op!(self, other, op);
    }

    #[inline]
    pub(crate) fn inplace_bitwise_and(&mut self, other: &Arbi) {
        self.inplace_bitwise_op(other, BitwiseOp::And);
    }

    #[inline]
    pub(crate) fn inplace_bitwise_ior(&mut self, other: &Arbi) {
        self.inplace_bitwise_op(other, BitwiseOp::Ior);
    }

    #[inline]
    pub(crate) fn inplace_bitwise_xor(&mut self, other: &Arbi) {
        self.inplace_bitwise_op(other, BitwiseOp::Xor);
    }

    #[inline]
    pub(crate) fn assign_bitwise_and(&mut self, a: &Arbi, b: &Arbi) {
        self.assign_bitwise_operation(a, b, BitwiseOp::And)
    }

    #[inline]
    pub(crate) fn assign_bitwise_ior(&mut self, a: &Arbi, b: &Arbi) {
        self.assign_bitwise_operation(a, b, BitwiseOp::Ior)
    }

    #[inline]
    pub(crate) fn assign_bitwise_xor(&mut self, a: &Arbi, b: &Arbi) {
        self.assign_bitwise_operation(a, b, BitwiseOp::Xor)
    }
}

#[cfg(test)]
mod tests {
    use super::BitwiseOp;
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::{Arbi, DDigit, Digit};
    use core::ops::RangeInclusive;

    struct BitwiseTestCase {
        name: &'static str,
        lrng: RangeInclusive<i128>,
        rrng: RangeInclusive<i128>,
    }

    fn test_bitwise_operation(
        result: &mut Arbi,
        r_1: i128,
        r_2: i128,
        op: BitwiseOp,
    ) -> i128 {
        let arbi_1 = Arbi::from(r_1);
        let arbi_2 = Arbi::from(r_2);
        match op {
            BitwiseOp::And => {
                let mut t_1 = Arbi::from(r_1);
                let t_2 = Arbi::from(r_2);
                t_1.inplace_bitwise_and(&t_2);
                assert_eq!(t_1, r_1 & r_2);

                result.assign_bitwise_and(&arbi_1, &arbi_2);
                r_1 & r_2
            }
            BitwiseOp::Ior => {
                let mut t_1 = Arbi::from(r_1);
                let t_2 = Arbi::from(r_2);
                t_1.inplace_bitwise_ior(&t_2);
                assert_eq!(t_1, r_1 | r_2);

                result.assign_bitwise_ior(&arbi_1, &arbi_2);
                r_1 | r_2
            }
            BitwiseOp::Xor => {
                let mut t_1 = Arbi::from(r_1);
                let t_2 = Arbi::from(r_2);
                t_1.inplace_bitwise_xor(&t_2);
                assert_eq!(t_1, r_1 ^ r_2);

                result.assign_bitwise_xor(&arbi_1, &arbi_2);
                r_1 ^ r_2
            }
        }
    }

    #[test]
    fn test_bitwise_operations() {
        let test_cases = vec![
            BitwiseTestCase {
                name: "32-bit integers",
                lrng: (i32::MIN as i128)..=(i32::MAX as i128),
                rrng: (i32::MIN as i128)..=(i32::MAX as i128),
            },
            BitwiseTestCase {
                name: "64-bit integers",
                lrng: (i64::MIN as i128)..=(i64::MAX as i128),
                rrng: (i64::MIN as i128)..=(i64::MAX as i128),
            },
            BitwiseTestCase {
                name: "128-bit integers",
                lrng: i128::MIN..=i128::MAX,
                rrng: i128::MIN..=i128::MAX,
            },
            BitwiseTestCase {
                name: "(32-bit LHS, 64-bit RHS)",
                lrng: (i32::MIN as i128)..=(i32::MAX as i128),
                rrng: (i64::MIN as i128)..=(i64::MAX as i128),
            },
            BitwiseTestCase {
                name: "(Nonnegative 32-bit LHS, complete 64-bit RHS)",
                lrng: 0..=(i32::MAX as i128),
                rrng: (i64::MIN as i128)..=(i64::MAX as i128),
            },
            BitwiseTestCase {
                name: "(Negative 32-bit LHS, complete 64-bit RHS)",
                lrng: (i32::MIN as i128)..=-1,
                rrng: (i64::MIN as i128)..=(i64::MAX as i128),
            },
            BitwiseTestCase {
                name: "(Nonnegative 64-bit LHS, complete 128-bit RHS)",
                lrng: 0..=(i64::MAX as i128),
                rrng: i128::MIN..=i128::MAX,
            },
            BitwiseTestCase {
                name: "(Negative 64-bit LHS, complete 128-bit RHS)",
                lrng: (i64::MIN as i128)..=1,
                rrng: i128::MIN..=i128::MAX,
            },
            BitwiseTestCase {
                name: "(Nonnegative 32-bit LHS, complete 128-bit RHS)",
                lrng: 0..=(i32::MAX as i128),
                rrng: (i64::MIN as i128)..=(i64::MAX as i128),
            },
            BitwiseTestCase {
                name: "(Negative 32-bit LHS, complete 128-bit RHS)",
                lrng: (i32::MIN as i128)..=-1,
                rrng: i128::MIN..=i128::MAX,
            },
        ];

        let operations = [BitwiseOp::And, BitwiseOp::Ior, BitwiseOp::Xor];

        let (mut rng, seed) = get_seedable_rng();
        let mut result = Arbi::zero();

        for test_case in test_cases {
            let lhs_die =
                get_uniform_die(*test_case.lrng.start(), *test_case.lrng.end());
            let rhs_die =
                get_uniform_die(*test_case.rrng.start(), *test_case.rrng.end());

            for &op in &operations {
                let test_name = format!(
                    "{} with {:?} [LHS range: {}-{}, RHS range: {}-{}]",
                    test_case.name,
                    op,
                    *test_case.lrng.start(),
                    *test_case.lrng.end(),
                    *test_case.rrng.start(),
                    *test_case.rrng.end()
                );

                for _ in 0..i16::MAX {
                    let r_1 = lhs_die.sample(&mut rng);
                    let r_2 = rhs_die.sample(&mut rng);

                    let expected =
                        test_bitwise_operation(&mut result, r_1, r_2, op);

                    assert_eq!(
                        result, expected,
                        "Failed {} test with LHS {}, RHS {}, and seed {}",
                        test_name, r_1, r_2, seed
                    );
                }
            }
        }
    }

    #[test]
    fn test_bitwise_special_cases_and_patterns() {
        let mut result = Arbi::zero();
        let operations = [BitwiseOp::And, BitwiseOp::Ior, BitwiseOp::Xor];

        let test_values = [
            (0, "zero"),
            (84, "small positive"),
            (-84, "small negative"),
            (-1, "all 1s"),
            (-1_i128 >> 1, "-1 >> 1"),
            (0x5555_5555_5555_5555_i128, "...010101"),
            (0xAAAA_AAAA_AAAA_AAAA_i128, "...101010"),
            (i32::MIN as i128, "32-bit min"),
            (i32::MAX as i128, "32-bit max"),
            (i64::MIN as i128, "64-bit min"),
            (i64::MAX as i128, "64-bit max"),
            (i128::MIN, "128-bit min"),
            (i128::MAX, "128-bit max"),
            (Digit::MAX as i128, "digit max"),
            (DDigit::MAX as i128, "double digit max"),
            (1_i128 << 31, "1 << 31"),
            (1_i128 << 32, "1 << 32"),
            (1_i128 << 63, "1 << 63"),
            (1_i128 << 64, "1 << 64"),
            (1_i128 << 127, "1 << 127"),
            (0xFFFF_i128, "16 ones"),
            (0xFFFF_FFFF_i128, "32 ones"),
            (0xFFFF_FFFF_FFFF_FFFF_i128, "64 ones"),
            (0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_i128, "96 ones"),
        ];

        for (a, a_description) in test_values {
            for (b, b_description) in test_values {
                for &op in &operations {
                    let expected =
                        test_bitwise_operation(&mut result, a, b, op);
                    assert_eq!(
                        result, expected,
                        "Failed special test with {} ({}) {:?} {} ({})",
                        a_description, a, op, b_description, b
                    );
                }
            }
        }
    }
}
