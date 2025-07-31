/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/* TODO: move to integration tests and clean up. */

#[cfg(test)]
mod tests {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{DDigit, SDDigit, SDigit};

    #[test]
    fn test_add() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let zero = Arbi::zero();

        assert_eq!(&a + &b, 5);
        assert_eq!(&b + &a, 5);
        assert_eq!(&a + &zero, 10);
        assert_eq!(&zero + &a, 10);
        assert_eq!(&b + &zero, -5);
        assert_eq!(&zero + &b, -5);
        assert_eq!(&a + &a, 20);
        assert_eq!(&b + &b, -10);

        // Important edge case
        let c = Arbi::from(DDigit::MAX);
        let d = c.clone();

        #[cfg(not(target_pointer_width = "64"))]
        assert_eq!(d + c, 36893488147419103230_u128);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(
            d + c,
            Arbi::from_str_radix("680564733841876926926749214863536422910", 10)
                .unwrap()
        );
    }

    #[test]
    fn test_add_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) =
                (die_sd.sample(&mut rng), die_sd.sample(&mut rng));
            let (mut a, b) = (Arbi::from(a_in), Arbi::from(b_in));

            assert_eq!(&a + &b, a_in as SDDigit + b_in as SDDigit);

            a += b;
            assert_eq!(a, a_in as SDDigit + b_in as SDDigit)
        }
    }

    #[test]
    fn test_sub() {
        let a = Arbi::from(10);
        let b = Arbi::from(-5);
        let z = Arbi::zero();

        assert_eq!(&a - &b, 15);
        assert_eq!(&b - &a, -15);
        assert_eq!(&a - &z, 10);
        assert_eq!(&z - &a, -10);
        assert_eq!(&z - &b, 5);
        assert_eq!(&b - &z, -5);
        assert_eq!(&a - &a, 0);
        assert_eq!(&b - &b, 0);
    }

    #[test]
    fn test_sub_smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sd = get_uniform_die(SDigit::MIN, SDigit::MAX);

        for _ in 0..i16::MAX {
            let (a_in, b_in) =
                (die_sd.sample(&mut rng), die_sd.sample(&mut rng));
            let (mut a, b) = (Arbi::from(a_in), Arbi::from(b_in));

            assert_eq!(&a - &b, a_in as SDDigit - b_in as SDDigit);

            a -= &b;
            assert_eq!(a, a_in as SDDigit - b_in as SDDigit);
        }
    }

    #[test]
    fn test_add_assign() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);
        a += &b;
        assert_eq!(a, 5);

        let mut a = Arbi::from(99090);
        let b = Arbi::from(9909032932_u64);
        a += &b;
        assert_eq!(a, 9909132022_u64);

        let mut c = Arbi::from(7);
        c += c.clone(); // Can't do c += &c
        assert_eq!(c, 14);
    }

    #[test]
    fn test_sub_assign() {
        let mut a = Arbi::from(10);
        let b = Arbi::from(-5);
        a -= &b;
        assert_eq!(a, 15);
        assert_eq!(b, -5);

        let mut c = Arbi::from(7);
        c -= c.clone(); // Can't do c -= &c
        assert_eq!(c, 0);
    }
}

#[cfg(test)]
mod test_add_with_integral {
    #[cfg(not(target_pointer_width = "64"))]
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    #[cfg(not(target_pointer_width = "64"))]
    use crate::{SDDigit, SDigit};

    #[test]
    fn test_add_zero() {
        let mut a = Arbi::zero();
        assert_eq!(&a + 0, 0);
        a = Arbi::from(123456789);
        assert_eq!(a + 0, 123456789);

        let mut a = Arbi::zero();
        assert_eq!(0 + &a, 0);
        a = Arbi::from(123456789);
        assert_eq!(0 + a, 123456789);
    }

    #[test]
    fn test_add_with_digit_or_less() {
        let mut a = Arbi::zero();
        let rhs = 1216627769;
        assert_eq!(&a + rhs, rhs);
        a = Arbi::from(rhs);
        assert_eq!(a + rhs, 2 * rhs as i64);

        let mut a = Arbi::zero();
        let rhs = 1216627769;
        assert_eq!(rhs + &a, rhs);
        a = Arbi::from(rhs);
        assert_eq!(rhs + a, 2 * rhs as i64);
    }

    #[test]
    fn test_add_with_more_than_a_digit() {
        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = 1118690935960365665i64;
        assert_eq!(&a + rhs, expected);
        assert_eq!(a + rhs, expected);

        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = 1118690935960365665i64;
        assert_eq!(rhs + &a, expected);
        assert_eq!(rhs + a, expected);
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            let lhs = die_sddigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(&lhs_arbi + rhs, lhs as SQDigit + rhs as SQDigit);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(lhs_arbi + rhs, lhs as SQDigit + rhs as SQDigit);

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(&lhs_arbi + rhs, lhs as SDDigit + rhs as SDDigit);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(lhs_arbi + rhs, lhs as SQDigit + rhs as SQDigit);

            let lhs = die_sddigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(rhs + &lhs_arbi, lhs as SQDigit + rhs as SQDigit);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(rhs + lhs_arbi, lhs as SQDigit + rhs as SQDigit);

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(rhs + &lhs_arbi, lhs as SDDigit + rhs as SDDigit);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(rhs + lhs_arbi, lhs as SQDigit + rhs as SQDigit);
        }
    }

    #[test]
    #[cfg(not(target_pointer_width = "64"))]
    fn smoke_3_to_4_digits() {
        let (mut rng, _) = get_seedable_rng();
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            let lhs = die_sqdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_add(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(&lhs_arbi + rhs, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_add(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(lhs_arbi + rhs, expected);

            let lhs = die_sqdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_add(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs + &lhs_arbi, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_add(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs + lhs_arbi, expected);
        }
    }
}

#[cfg(test)]
mod test_sub_with_integral {
    use crate::util::test::{get_seedable_rng, get_uniform_die, Distribution};
    use crate::Arbi;
    use crate::{SDDigit, SDigit, SQDigit};

    #[test]
    fn test_sub_zero() {
        let mut a = Arbi::zero();
        assert_eq!(&a - 0, 0);
        a = Arbi::from(123456789);
        assert_eq!(a - 0, 123456789);

        let mut a = Arbi::zero();
        assert_eq!(0 - &a, 0);
        a = Arbi::from(123456789);
        assert_eq!(0 - a, -123456789);
    }

    #[test]
    fn test_sub_with_digit_or_less() {
        let mut a = Arbi::zero();
        let rhs = 1216627769_i64;
        assert_eq!(&a - rhs, -rhs);
        a = Arbi::from(-rhs);
        assert_eq!(a - rhs, -2 * rhs as i64);

        let mut a = Arbi::zero();
        let rhs = 1216627769;
        assert_eq!(rhs - &a, rhs);
        a = Arbi::from(rhs);
        assert_eq!(rhs - a, 0);
    }

    #[test]
    fn test_sub_with_more_than_a_digit() {
        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = -1118937849538567889i64;
        assert_eq!(&a - rhs, expected);
        assert_eq!(a - rhs, expected);

        let a = Arbi::from(-123456789101112i64);
        let rhs = 1118814392749466777i64;
        let expected = 1118937849538567889i64;
        assert_eq!(rhs - &a, expected);
        assert_eq!(rhs - a, expected);
    }

    #[test]
    fn smoke() {
        let (mut rng, _) = get_seedable_rng();
        let die_sdigit = get_uniform_die(SDigit::MIN, SDigit::MAX);
        let die_sddigit = get_uniform_die(SDDigit::MIN, SDDigit::MAX);

        for _ in 0..i16::MAX {
            let lhs = die_sddigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(
                &lhs_arbi - rhs,
                SQDigit::try_from(lhs).unwrap()
                    - SQDigit::try_from(rhs).unwrap()
            );
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(
                lhs_arbi - rhs,
                SQDigit::try_from(lhs).unwrap()
                    - SQDigit::try_from(rhs).unwrap()
            );

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(&lhs_arbi - rhs, lhs as SDDigit - rhs as SDDigit);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(
                lhs_arbi - rhs,
                SQDigit::try_from(lhs).unwrap()
                    - SQDigit::try_from(rhs).unwrap()
            );

            let lhs = die_sddigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(
                rhs - &lhs_arbi,
                SQDigit::try_from(rhs).unwrap()
                    - SQDigit::try_from(lhs).unwrap()
            );
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(
                rhs - lhs_arbi,
                SQDigit::try_from(rhs).unwrap()
                    - SQDigit::try_from(lhs).unwrap()
            );

            let lhs = die_sdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sdigit.sample(&mut rng);
            assert_eq!(rhs - &lhs_arbi, rhs as SDDigit - lhs as SDDigit);
            let rhs = die_sddigit.sample(&mut rng);
            assert_eq!(
                rhs - lhs_arbi,
                SQDigit::try_from(rhs).unwrap()
                    - SQDigit::try_from(lhs).unwrap()
            );
        }
    }

    #[cfg(not(target_pointer_width = "64"))]
    #[test]
    fn smoke_3_to_4_digits() {
        let (mut rng, _) = get_seedable_rng();
        let die_sqdigit = get_uniform_die(SQDigit::MIN, SQDigit::MAX);

        for _ in 0..i16::MAX {
            let lhs = die_sqdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_sub(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(&lhs_arbi - rhs, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (lhs as SQDigit).checked_sub(rhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(lhs_arbi - rhs, expected);

            let lhs = die_sqdigit.sample(&mut rng);
            let lhs_arbi = Arbi::from(lhs);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (rhs as SQDigit).checked_sub(lhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs - &lhs_arbi, expected);
            let rhs = die_sqdigit.sample(&mut rng);
            let expected = match (rhs as SQDigit).checked_sub(lhs as SQDigit) {
                None => continue,
                Some(v) => v,
            };
            assert_eq!(rhs - lhs_arbi, expected);
        }
    }
}
