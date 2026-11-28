/*
Copyright 2024-2026 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::from_string::{configs::BASE_MBS, BaseMbs, ParseError};
use crate::{Arbi, Base, Digit, Pow};
use alloc::vec::Vec;

/// Applies when the base is not a power of two. Cutoff unit is in "batch"es.
/// See `assign_str_radix_algo_generic` for meaning of a "batch".
///
/// Determined empirically via `tune_divide_and_conquer_cutoff` below. Revisit
/// each time multiplication code becomes faster.
const FROM_STR_DIVIDE_AND_CONQUER_CUTOFF: usize = 1000;

impl Arbi {
    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
    ///
    /// <div class="warning">
    ///
    /// If a parsing error is returned, `self`'s value may be different from its
    /// original.
    ///
    /// </div>
    ///
    /// # Panic
    /// Panics if `radix` is not in \\( [2, 36] \\). Use
    /// [`Arbi::assign_str_base`] for a panic-free version.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, ParseError};
    ///
    /// let mut x = Arbi::with_capacity(10);
    /// assert_eq!(x, 0);
    ///
    /// match x.assign_str_radix("123456789", 10) {
    ///     Ok(_) => assert_eq!(x, 123456789),
    ///     Err(e) => match e {
    ///         ParseError::InvalidDigit => panic!("invalid digit"),
    ///         ParseError::Empty => panic!("empty string"),
    ///     },
    /// }
    ///
    /// x.assign_str_radix("7c2ecdfacad74e0f0101b", 16).unwrap();
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// Panics on invalid `radix` values
    /// ```should_panic
    /// use arbi::Arbi;
    /// let mut x = Arbi::with_capacity(5);
    /// x.assign_str_radix("7c2ecdfacad74e0f0101b", 37);
    /// ```
    ///
    /// Example invalid strings
    /// ```
    /// use arbi::{Arbi, ParseError};
    ///
    /// let mut a = Arbi::zero();
    ///
    /// assert!(matches!(a.assign_str_radix("", 10), Err(ParseError::Empty)));
    /// assert!(matches!(
    ///     a.assign_str_radix("   - ", 10),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// assert!(matches!(
    ///     a.assign_str_radix("ffff", 10),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// ```
    pub fn assign_str_radix(
        &mut self,
        s: &str,
        radix: u32,
    ) -> Result<(), ParseError> {
        let base = match Base::try_from(radix) {
            Ok(b) => b,
            Err(_) => panic!("Invalid radix {radix}"),
        };
        self.assign_str_base(s, base)
    }

    /// Assign the integer value the provided string represents to this `Arbi`
    /// integer.
    ///
    /// <div class="warning">
    ///
    /// If a parsing error is returned, `self`'s value may be different from its
    /// original.
    ///
    /// </div>
    ///
    /// # Examples
    /// ```
    /// use arbi::{
    ///     base::{DEC, HEX},
    ///     Arbi, ParseError,
    /// };
    ///
    /// let mut x = Arbi::with_capacity(10);
    /// assert_eq!(x, 0);
    ///
    /// match x.assign_str_base("123456789", DEC) {
    ///     Ok(_) => assert_eq!(x, 123456789),
    ///     Err(e) => match e {
    ///         ParseError::InvalidDigit => panic!("invalid digit"),
    ///         ParseError::Empty => panic!("empty string"),
    ///     },
    /// }
    ///
    /// x.assign_str_base("7c2ecdfacad74e0f0101b", HEX).unwrap();
    /// assert_eq!(x, 0x7c2ecdfacad74e0f0101b_u128);
    /// ```
    ///
    /// Example invalid strings:
    /// ```
    /// use arbi::{base::DEC, Arbi, ParseError};
    ///
    /// let mut a = Arbi::zero();
    ///
    /// assert!(matches!(a.assign_str_base("", DEC), Err(ParseError::Empty)));
    /// assert!(matches!(
    ///     a.assign_str_base("   - ", DEC),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// assert!(matches!(
    ///     a.assign_str_base("ffff", DEC),
    ///     Err(ParseError::InvalidDigit)
    /// ));
    /// ```
    pub fn assign_str_base(
        &mut self,
        s: &str,
        base: Base,
    ) -> Result<(), ParseError> {
        let (base_digits, has_minus_sign) =
            Self::parse_str_sign_skip_leading_zeros(s)?;
        if base_digits.is_empty() {
            self.make_zero();
            return Ok(());
        }

        let base_value = base.value() as u32;

        let capacity = Self::size_with_size_base_maybe_over_by_one(
            base_value,
            base_digits.len(),
        );
        self.vec.clear();
        self.vec.reserve(capacity);

        #[cfg(debug_assertions)]
        let initial_capacity = self.vec.capacity();

        self.neg = has_minus_sign;

        if base_value.is_power_of_two() {
            self.assign_str_radix_algo_pow2(base_digits, base_value)?
        } else if base_digits.len()
            <= BASE_MBS[base_value as usize].mbs
                * FROM_STR_DIVIDE_AND_CONQUER_CUTOFF
        {
            self.assign_str_radix_algo_generic(base_digits, base_value)?
        } else {
            let magnitude = Self::from_str_radix_algo_divide_and_conquer(
                base_digits,
                base_value,
                FROM_STR_DIVIDE_AND_CONQUER_CUTOFF,
            )?;
            // Copy, not move; use `self`s existing reserved memory.
            self.vec.extend_from_slice(&magnitude.vec);
        }

        #[cfg(debug_assertions)]
        {
            debug_assert_eq!(self.vec.capacity(), initial_capacity);
            debug_assert!(
                self.vec.len() == capacity || self.vec.len() == capacity - 1
            );
        }

        Ok(())
    }

    fn assign_str_radix_algo_pow2(
        &mut self,
        base_digits: &[u8],
        base: u32,
    ) -> Result<(), ParseError> {
        debug_assert!(!base_digits.is_empty());
        debug_assert!((2..=36).contains(&base) && base.is_power_of_two());

        // Number of bits in a base-`base` digit.
        let bits_in_base_digit: u32 = base.trailing_zeros();
        let mut shift: u32 = 0;
        let mut digit: Digit = 0;
        for &c in base_digits.iter().rev() {
            let base_digit: Digit = match (c as char).to_digit(base) {
                Some(base_digit) => base_digit as Digit,
                None => return Err(ParseError::InvalidDigit),
            };
            digit |= base_digit << shift;
            shift += bits_in_base_digit;
            if Digit::BITS <= shift {
                self.vec.push(digit);
                shift -= Digit::BITS;
                /*
                    On Digit::BITS == shift, digit is simply reset to 0.
                    On Digit::BITS < shift, digit will be set to the remaining
                    bits in the current base digit that could not fit in the
                    just pushed Arbi::BASE-digit, so no information is lost.
                */
                digit = base_digit >> (bits_in_base_digit - shift);
            }
        }
        if digit != 0 {
            self.vec.push(digit);
        }

        Ok(())
    }

    /// "Divide and conquer"-based string to integer algorithm. Implements
    /// Algorithm 1.25 FastIntegerInput from Brent and Zimmermann, Modern
    /// Computer Arithmetic (section 1.7.2), which is based on the following
    /// observation. If S = S_hi || S_lo where || denotes concatenation and S_lo
    /// has k digits in base B, then
    ///
    /// ```text
    /// Value(S) = Value(S_hi) * B^k + Value(S_lo)
    /// ```
    ///
    /// where Value(t) is the value of t in base B.
    ///
    /// Leading zeros are permitted.
    ///
    /// Returns the magnitude.
    fn from_str_radix_algo_divide_and_conquer(
        base_digits: &[u8],
        base: u32,
        cutoff: usize,
    ) -> Result<Arbi, ParseError> {
        debug_assert!((2..=36).contains(&base) && !base.is_power_of_two());
        debug_assert!(cutoff >= 1);
        debug_assert!(!base_digits.is_empty());

        let BaseMbs { mbs, base_pow_mbs } = BASE_MBS[base as usize];

        // Divide into smallest power of two number of pieces such that a piece
        // has at most `cutoff` batches.
        let batches = (base_digits.len() + mbs - 1) / mbs;
        let mut pieces = 1;
        while batches > pieces * cutoff {
            pieces *= 2;
        }
        let batches_per_piece = (batches + pieces - 1) / pieces;
        let piece_len = mbs * batches_per_piece;

        // l <- [val(s_0), val(s_1), ..., val(s_{m-1})], s_0 least significant;
        // s_{m-1} may have fewer than piece_len base digits.
        let mut l: Vec<Arbi> =
            Vec::with_capacity(base_digits.len() / piece_len + 1);
        for s in base_digits.rchunks(piece_len) {
            let mut val = Arbi::zero();
            val.vec.reserve(s.len() / mbs + 1);
            val.assign_str_radix_algo_generic(s, base)?;
            l.push(val);
        }
        let m = l.len();
        if m == 1 {
            return Ok(l.swap_remove(0));
        }

        // (b, k) <- (B^piece_len, m)
        let mut b = Arbi::from(base_pow_mbs).pow(batches_per_piece);
        let mut k = m;
        while k > 1 {
            // k even: l <- [l_0 + bl_1, l_2 + bl_3, ..., l_{k-2} + bl_{k-1}]
            // else  : l <- [l_0 + bl_1, l_2 + bl_3, ..., l_{k-1}]
            for i in 0..k / 2 {
                let l_even = core::mem::take(&mut l[2 * i]);
                let l_odd = core::mem::take(&mut l[2 * i + 1]);
                l[i] = l_even + l_odd * &b;
            }
            if k % 2 == 1 {
                l.swap(k / 2, k - 1);
            }
            // (b, k) <- (b^2, ceil(k / 2))
            k = (k + 1) / 2;
            l.truncate(k);
            if k > 1 {
                b = &b * &b;
            }
        }

        // return l_0
        Ok(l.swap_remove(0))
    }

    /* Generic Algorithm (works for all valid bases) */
    ///
    /// `self` assumed to be zero on entry. Leading zeros in the string are
    /// permitted.
    fn assign_str_radix_algo_generic(
        &mut self,
        base_digits: &[u8],
        base: u32,
    ) -> Result<(), ParseError> {
        debug_assert!(!base_digits.is_empty());
        debug_assert!((2..=36).contains(&base));

        let BaseMbs { mbs, base_pow_mbs } = BASE_MBS[base as usize];
        let n_base = base_digits.len();
        let rem_batch_size = n_base % mbs;
        let mut pos = 0;

        /* Handle first partial chunk */
        if rem_batch_size > 0 {
            // Initialize batch value
            let mut batch: Digit = 0;
            // Convert batch substring to integer value
            let end = pos + rem_batch_size;
            while pos < end {
                match (base_digits[pos] as char).to_digit(base) {
                    Some(base_digit) => {
                        batch = base_digit as Digit + batch * base as Digit;
                        pos += 1;
                    }
                    None => return Err(ParseError::InvalidDigit),
                }
            }
            self.vec.push(batch);
        }

        /* Process remaining full-size chunks */
        while pos < n_base {
            // Initialize batch value
            let mut batch: Digit = 0;
            // Convert batch substring to integer value
            let end = pos + mbs;
            while pos < end {
                match (base_digits[pos] as char).to_digit(base) {
                    Some(base_digit) => {
                        batch = base_digit as Digit + batch * base as Digit;
                        pos += 1;
                    }
                    None => return Err(ParseError::InvalidDigit),
                }
            }
            Self::imul1add1(self, base_pow_mbs, Some(batch));
        }

        self.trim();

        Ok(())
    }

    pub(crate) fn parse_str_sign(s: &str) -> Result<(&[u8], bool), ParseError> {
        if s.is_empty() {
            return Err(ParseError::Empty);
        }

        let s = s.as_bytes();

        let (base_digits, has_minus_sign) = match s {
            [b'-' | b'+'] => {
                return Err(ParseError::InvalidDigit);
            }
            [b'-', rest @ ..] => (rest, true),
            [b'+', rest @ ..] => (rest, false),
            _ => (s, false),
        };
        debug_assert!(!base_digits.is_empty());

        Ok((base_digits, has_minus_sign))
    }

    pub(crate) fn parse_str_sign_skip_leading_zeros(
        s: &str,
    ) -> Result<(&[u8], bool), ParseError> {
        let (mut base_digits, has_minus_sign) = Self::parse_str_sign(s)?;
        while let [c, rest @ ..] = base_digits {
            if *c != b'0' {
                break;
            }
            base_digits = rest;
        }
        Ok((base_digits, has_minus_sign))
    }

    #[allow(dead_code)]
    pub(crate) fn validate_str_base(
        s: &str,
        base: Base,
    ) -> Result<(&[u8], bool), ParseError> {
        let (mut base_digits, has_minus_sign) = Self::parse_str_sign(s)?;

        let base: u32 = base.value() as u32;

        while let [c, rest @ ..] = base_digits {
            let _ = match (*c as char).to_digit(base) {
                Some(value) => value,
                None => {
                    return Err(ParseError::InvalidDigit);
                }
            };

            base_digits = rest;
        }

        Ok((base_digits, has_minus_sign))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::DEC;
    use crate::util::test::Rng;
    use crate::{
        util::test::{get_seedable_rng, get_uniform_die, Distribution},
        DDigit, SDDigit,
    };
    use alloc::string::{String, ToString};
    use alloc::vec;
    use alloc::vec::Vec;

    #[test]
    fn test_assign_str_base() {
        let mut x = Arbi::zero();

        x.assign_str_base("0", DEC).unwrap();
        assert_eq!(&x, 0);

        x.assign_str_base("3239", DEC).unwrap();
        assert_eq!(&x, 3239);

        x.assign_str_base("-3239", DEC).unwrap();
        assert_eq!(&x, -3239);
    }

    #[test]
    #[should_panic]
    fn assign_str_base_empty_string() {
        let mut x = Arbi::zero();
        x.assign_str_base("", DEC).unwrap();
    }

    #[test]
    #[should_panic]
    fn assign_str_base_from_bad_string() {
        let mut x = Arbi::zero();
        x.assign_str_base("  -", DEC).unwrap();
    }

    #[test]
    fn misc() {
        let mut x = Arbi::zero();
        let s = "999909090093232329302932309230930923230992094029424204";
        let u = "-999909090093232329302932309230930923230992094029424204";

        x.assign_str_base(s, DEC).unwrap();
        assert_eq!(x.to_string_base(10.try_into().unwrap()), s);

        x.assign_str_base(u, DEC).unwrap();
        assert_eq!(x.to_string_base(10.try_into().unwrap()), u);

        let sddigit_min: String = SDDigit::MIN.to_string();
        let ddigit_max: String = DDigit::MAX.to_string();

        x.assign_str_base(&sddigit_min, DEC).unwrap();
        assert_eq!(&x, SDDigit::MIN);
        x.assign_str_base(&ddigit_max, DEC).unwrap();
        assert_eq!(&x, DDigit::MAX);
    }

    #[test]
    fn smoke() {
        let mut x = Arbi::zero();

        let (mut rng, _) = get_seedable_rng();
        let die = get_uniform_die(SDDigit::MIN, SDDigit::MAX);
        let die_16 = get_uniform_die(i16::MIN, i16::MAX);

        for _ in 0..i16::MAX {
            let rv: SDDigit = die.sample(&mut rng);
            let s: String = rv.to_string();
            x.assign_str_base(&s, DEC).unwrap();
            assert_eq!(&x, rv);

            let rv_16: i16 = die_16.sample(&mut rng);
            let s: String = rv_16.to_string();
            x.assign_str_base(&s, DEC).unwrap();
            assert_eq!(&x, rv_16);
        }
    }

    /* Divide and conquer */

    /// Not a test. Measures when the divide and conquer algorithm begins to
    /// beat the generic quadratic algorithm. Helps choosing
    /// `FROM_STR_DIVIDE_AND_CONQUER_CUTOFF`.
    ///
    /// ```text
    /// cargo test --release -p arbi tune_divide_and_conquer_cutoff -- --ignored --nocapture
    /// ```
    #[test]
    #[ignore = "tuning utility, not a test"]
    fn tune_divide_and_conquer_cutoff() {
        extern crate std;
        use std::println;
        use std::time::Instant;

        fn time<F: FnMut()>(mut f: F) -> f64 {
            let start = Instant::now();
            f();
            let once = start.elapsed().as_nanos().max(1) as f64;
            let calls = ((2.0e6 / once) as usize).clamp(1, 100_000);
            let mut best = f64::MAX;
            for _ in 0..12 {
                let start = Instant::now();
                for _ in 0..calls {
                    f();
                }
                best =
                    best.min(start.elapsed().as_nanos() as f64 / calls as f64);
            }
            best
        }

        // `core::hint::black_box` not in Rust 1.65.
        let mut sink = 0usize;

        let (mut rng, _) = get_seedable_rng();
        let base = 10;
        let mbs = BASE_MBS[base as usize].mbs;
        println!(
            "\ncurrent FROM_STR_DIVIDE_AND_CONQUER_CUTOFF = {}",
            FROM_STR_DIVIDE_AND_CONQUER_CUTOFF
        );

        let candidates = [400usize, 600, 800, 1000, 1200, 1600, 2400];
        let sizes = [
            500usize, 700, 900, 1100, 1300, 1600, 2000, 2500, 3000, 4096, 5000,
            8192, 11111, 16384,
        ];
        std::print!("\n{:>8}", "batches");
        for cutoff in candidates {
            std::print!("{:>8}", cutoff);
        }
        println!("  (time relative to quadratic, by cutoff)");
        let mut log_sum = [0.0f64; 7];
        let mut worst = [0.0f64; 7];
        for batches in sizes {
            let s = random_base_digits(&mut rng, batches * mbs, base);
            let t_quadratic = time(|| {
                sink += quadratic(&s, base).unwrap().size();
            });
            std::print!("{:>8}", batches);
            for (j, cutoff) in candidates.into_iter().enumerate() {
                let ratio = if batches <= cutoff {
                    1.0
                } else {
                    let t = time(|| {
                        sink += Arbi::from_str_radix_algo_divide_and_conquer(
                            &s, base, cutoff,
                        )
                        .unwrap()
                        .size();
                    });
                    t / t_quadratic
                };
                log_sum[j] += ratio.ln();
                worst[j] = worst[j].max(ratio);
                std::print!("{:>8.3}", ratio);
            }
            println!();
        }
        std::print!("{:>8}", "geomean");
        for sum in log_sum {
            std::print!("{:>8.3}", (sum / sizes.len() as f64).exp());
        }
        std::print!("\n{:>8}", "worst");
        for w in worst {
            std::print!("{:>8.3}", w);
        }
        println!();
        println!("\n(checksum {})", sink);
    }

    const DIGIT_CHARS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";

    /// Non-powers-of-two bases
    fn general_bases() -> impl Iterator<Item = u32> {
        (2..=36u32).filter(|b| !b.is_power_of_two())
    }

    /// Quadratic algorithm; leading zeros permitted on string
    fn quadratic(base_digits: &[u8], base: u32) -> Result<Arbi, ParseError> {
        let mut x = Arbi::zero();
        x.assign_str_radix_algo_generic(base_digits, base)?;
        Ok(x)
    }

    /// `len` random base-`base` digits; leading zeros permitted.
    fn random_base_digits<R: Rng>(
        rng: &mut R,
        len: usize,
        base: u32,
    ) -> Vec<u8> {
        let die = get_uniform_die(0, base - 1);
        (0..len)
            .map(|_| DIGIT_CHARS[die.sample(rng) as usize])
            .collect()
    }

    fn assert_divide_and_conquer_eq_quadratic(
        base_digits: &[u8],
        base: u32,
        cutoff: usize,
    ) {
        let expected = quadratic(base_digits, base).unwrap();
        let actual = Arbi::from_str_radix_algo_divide_and_conquer(
            base_digits,
            base,
            cutoff,
        )
        .unwrap();
        assert!(
            actual == expected,
            "base {}, cutoff {}, length {}",
            base,
            cutoff,
            base_digits.len()
        );
    }

    #[test]
    fn divide_and_conquer_smoke() {
        let (mut rng, _) = get_seedable_rng();
        for base in general_bases() {
            let mbs = BASE_MBS[base as usize].mbs;
            let die_len = get_uniform_die(1, 40 * mbs);
            for cutoff in [1, 2, 3, 8] {
                for _ in 0..20 {
                    let len = die_len.sample(&mut rng);
                    let s = random_base_digits(&mut rng, len, base);
                    assert_divide_and_conquer_eq_quadratic(&s, base, cutoff);
                }
            }
        }
    }

    #[test]
    fn divide_and_conquer_batch_boundaries() {
        let (mut rng, _) = get_seedable_rng();
        for base in general_bases() {
            let mbs = BASE_MBS[base as usize].mbs;
            for cutoff in [1, 2, 3, 8] {
                for batches in [1, 2, 3, 4, 5, 8, 9, 16, 17, 33, 64] {
                    for len in
                        [batches * mbs - 1, batches * mbs, batches * mbs + 1]
                    {
                        let s = random_base_digits(&mut rng, len, base);
                        assert_divide_and_conquer_eq_quadratic(
                            &s, base, cutoff,
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn divide_and_conquer_zeros_and_max_digits() {
        for base in [3u32, 10, 36] {
            let mbs = BASE_MBS[base as usize].mbs;
            let max_digit = DIGIT_CHARS[base as usize - 1];
            for len in [37 * mbs + 5, 64 * mbs, 64 * mbs + 1] {
                // 00...00
                let zero = vec![b'0'; len];
                // 00...01
                let mut one = vec![b'0'; len];
                one[len - 1] = b'1';
                // 10...00 (power of the base)
                let mut power = vec![b'0'; len];
                power[0] = b'1';
                // Largest possible value with this many base digits
                let max = vec![max_digit; len];
                // Lone nonzero digit in middle of vec
                let mut middle = vec![b'0'; len];
                middle[len / 2] = max_digit;

                for s in [&zero, &one, &power, &max, &middle] {
                    for cutoff in [1, 5] {
                        assert_divide_and_conquer_eq_quadratic(s, base, cutoff);
                    }
                }
            }
        }
    }

    #[test]
    fn divide_and_conquer_invalid_digit() {
        let (mut rng, _) = get_seedable_rng();
        for base in [3u32, 10, 35] {
            let mbs = BASE_MBS[base as usize].mbs;
            let len = 20 * mbs + 3;
            let valid = random_base_digits(&mut rng, len, base);
            for bad in [DIGIT_CHARS[base as usize], b'!', b' ', b'-'] {
                for pos in [0, 1, mbs, len / 2, len - mbs, len - 1] {
                    let mut s = valid.clone();
                    s[pos] = bad;
                    for cutoff in [1, 4] {
                        let r = Arbi::from_str_radix_algo_divide_and_conquer(
                            &s, base, cutoff,
                        );
                        assert!(
                            matches!(r, Err(ParseError::InvalidDigit)),
                            "base {}, position {}",
                            base,
                            pos
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn long_strings_through_public_api() {
        let (mut rng, _) = get_seedable_rng();
        for base in [10u32, 7, 36] {
            let mbs = BASE_MBS[base as usize].mbs;
            let at_cutoff = mbs * FROM_STR_DIVIDE_AND_CONQUER_CUTOFF;
            for len in [at_cutoff - 1, at_cutoff, at_cutoff + 1, 3 * at_cutoff]
            {
                let mut s = random_base_digits(&mut rng, len, base);
                if s[0] == b'0' {
                    s[0] = b'1';
                }
                let expected = quadratic(&s, base).unwrap();
                let positive = String::from_utf8(s).unwrap();
                let negative = alloc::format!("-{}", positive);

                let x = Arbi::from_str_radix(&positive, base).unwrap();
                assert!(x == expected, "base {}, length {}", base, len);
                let x = Arbi::from_str_radix(&negative, base).unwrap();
                assert!(x == -&expected, "base {}, length {}", base, len);

                // Leading zeros, plus specified sign
                let padded = alloc::format!("+000{}", positive);
                let x = Arbi::from_str_radix(&padded, base).unwrap();
                assert!(x == expected, "base {}, length {}", base, len);

                // Assigning into integer that already has a value
                let mut y = Arbi::from(-12345);
                y.assign_str_radix(&positive, base).unwrap();
                assert!(y == expected, "base {}, length {}", base, len);

                // Invalid digit in middle
                let mut bad = positive.into_bytes();
                bad[len / 2] = b'!';
                let bad = String::from_utf8(bad).unwrap();
                assert!(matches!(
                    Arbi::from_str_radix(&bad, base),
                    Err(ParseError::InvalidDigit)
                ));
            }
        }
    }

    #[test]
    fn long_decimal_round_trip() {
        let (mut rng, _) = get_seedable_rng();
        let len = 19 * FROM_STR_DIVIDE_AND_CONQUER_CUTOFF * 2 + 7;
        let mut s = random_base_digits(&mut rng, len, 10);
        s[0] = b'9';
        let s = String::from_utf8(s).unwrap();
        let x: Arbi = s.parse().unwrap();
        assert_eq!(x.to_string(), s);
    }
}
