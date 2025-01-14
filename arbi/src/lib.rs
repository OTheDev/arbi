/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(test))]
extern crate alloc;
#[cfg(all(feature = "nightly", test))]
extern crate test;

use alloc::vec::Vec;

mod add;
mod assign;
mod assign_double;
mod assign_integral;
mod assign_string;
pub mod base;
mod bits;
mod bitwise;
mod builtin_int_methods;
mod capacity;
mod comparisons;
mod comparisons_double;
mod comparisons_integral;
mod display;
mod division;
#[cfg(not(doctest))]
#[allow(unknown_lints)]
#[allow(clippy::doc_lazy_continuation)]
pub mod doc;
mod exponentiation;
mod fits;
mod floor;
mod from_double;
mod from_integral;
mod from_string;
mod increment_decrement;
mod is_odd_is_even;
mod is_signed;
mod is_zero;
mod left_shift;
mod macros;
mod multiplication;
mod negate;
mod new;
mod print_internal;
mod random;
mod right_shift;
mod sign;
mod size;
mod to_double;
mod to_integral;
mod to_string;
mod to_twos_complement;
mod uints;
mod unary_ops;
mod util;
mod zero_and_one;

pub use assign::Assign;
pub use base::{Base, BaseError};
pub use exponentiation::Pow; // No PowAssign implementations yet
pub use fits::Fits;
pub use from_string::ParseError;
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub use random::RandomArbi;

/// Unsigned integer type representing a base-[`Arbi::BASE`] digit.
pub type Digit = u32;

/// Unsigned integer type used for counts of bits.
///
/// # Note
/// A [`Vec`] has maximum capacity of `isize::MAX` in bytes. The unsigned
/// integer type used to count bits must have width greater than `usize` in
/// order to represent the theoretical number of bits that can be used at
/// maximum capacity. Currently, a `u128` is used, which should accomodate most
/// systems today. A custom unsigned integer type might be created in the future
/// for future-proofing.
pub type BitCount = u128;

#[allow(dead_code)]
type SDigit = i32;

type DDigit = u64;
type SDDigit = i64;

#[allow(dead_code)]
type QDigit = u128;
#[allow(dead_code)]
type SQDigit = i128;

const DBL_MAX_INT: u64 = 0x20000000000000; // 2 ** 53

/// Arbitrary Precision Integer type.
///
/// # Internal Representation
/// The internal representation of an `Arbi` integer consists of a boolean field
/// encoding whether or not the integer is negative, as well as a [`Vec`] of
/// [`Digit`]s (an unsigned integer type) encoding the absolute value of the
/// integer with least significant digits first. A "digit" is a
/// base-[`Arbi::BASE`] digit (i.e. an integer in
/// \\( [0, \text{Arbi::BASE} - 1] = [0, \text{Digit::MAX}] \\)).
///
/// # Limits
/// - [`Arbi::MAX_CAPACITY`]: [`Vec`] is limited to `isize::MAX` bytes in
///   capacity. A digit has size in bytes `core::mem::size_of::<Digit>()`. The
///   maximum capacity is therefore `isize::MAX / core::mem::size_of::<Digit>()`.
/// - [`Arbi::MAX_BITS`]: At maximum capacity, [`Arbi::MAX_BITS`] bits are
///   available to represent the absolute value of the `Arbi` integer.
///
/// When resizing/reserving more space, if the needed space exceeds `isize::MAX`
/// in bytes, the `Vec` allocation methods currently used will panic to signal
/// `capacity overflow`. The `Vec` allocation methods also panic if the
/// allocator reports allocation failure. In practice, memory allocation
/// typically fails for less than `isize::MAX` in bytes.
///
/// In the future, we may choose to explicitly handle such errors to avoid a
/// panic, where it makes sense.
///
/// # Panic
/// In general:
/// - If an operation can panic, it will be clearly documented.
///
/// - Operations typically only panic because they are enforcing consistency
///   with the behavior of primitive integer types. For example, a division by
///   zero panics. Similarly, [`Arbi::from_str_radix()`] and
///   [`Arbi::to_string_radix()`] panic if the `radix` argument value is
///   invalid, consistent with the built-in analogues. [`Arbi::from_str_base()`]
///   and [`Arbi::to_string_base()`] are equivalent, except that they do not
///   panic on invalid bases.
///
/// - Because [`Vec`] is limited to `isize::MAX` bytes in capacity, if an
///   operation would lead to an `Arbi` requiring more than `isize::MAX` bytes
///   in capacity, then the current `Vec` allocation methods used will panic.
///   The `Vec` allocation methods also panic if the allocator reports
///   allocation failure. In practice, memory allocation typically fails for
///   less than `isize::MAX` in bytes.
///
/// - Some operations, such as exponentiation, might know in advance that the
///   result will need a capacity that will exceed `Vec`'s limits. In such
///   cases, the program will panic immediately, rather than allow it to run a
///   long computation that is guaranteed to exhaust memory.
#[derive(Clone, Debug, Default)]
pub struct Arbi {
    /// Stores the magnitude of this integer, least significant digits first
    /// (base `Digit::MAX + 1`).
    vec: Vec<Digit>,

    /// `true` if and only if this integer is strictly negative.
    neg: bool,
}

impl Arbi {
    /// Base used for the internal representation of the integer.
    #[allow(clippy::unnecessary_cast)]
    pub const BASE: DDigit = (1 as DDigit) << Digit::BITS;

    /// Take away trailing zeros in the internal digit vector until we find the
    /// most significant digit. If the vector is empty after this process, make
    /// this integer have value `0`.
    #[inline(always)]
    fn trim(&mut self) {
        while !self.vec.is_empty() && self.vec.last() == Some(&0) {
            self.vec.pop();
        }
        if self.vec.is_empty() {
            self.neg = false;
        }
    }

    /// Make this `Arbi` integer have value `0`, in-place.
    #[inline(always)]
    fn make_zero(&mut self) {
        self.vec.clear();
        self.neg = false;
    }

    /// Make this `Arbi` integer have value `1`, in-place.
    #[inline(always)]
    fn make_one(&mut self, neg: bool) {
        self.vec.resize(1, 0);
        self.vec[0] = 1;
        self.neg = neg;
    }

    /// Same as cloning but ensuring a given capacity prior.
    pub(crate) fn with_capacity_and_copy(capacity: usize, arbi: &Arbi) -> Self {
        let mut new_vec = Vec::with_capacity(capacity);
        new_vec.extend_from_slice(&arbi.vec);
        Self {
            vec: new_vec,
            neg: arbi.neg,
        }
    }

    // TODO: make from_digits(), from_slice(), ... type functions public, once
    // names have been decided.

    /// Return a new `Arbi` integer with magnitude given by `digits` (least
    /// significant digits first).
    ///
    /// No memory allocation occurs.
    #[allow(dead_code)]
    pub(crate) fn from_digits(digits: Vec<Digit>, is_negative: bool) -> Self {
        let mut arbi = Arbi {
            neg: is_negative,
            vec: digits,
        };
        arbi.trim();
        arbi
    }

    /// Return a new `Arbi` integer with magnitude given by `digits` (least
    /// significant digits first).
    #[allow(dead_code)]
    pub(crate) fn from_slice(digits: &[Digit], is_negative: bool) -> Self {
        let mut arbi = Arbi {
            neg: is_negative,
            vec: digits.to_vec(),
        };
        arbi.trim();
        arbi
    }

    /// Assign from a slice of `digits` representing the magnitude.
    ///
    /// No memory allocation occurs if the original internal digit vector has
    /// enough capacity to store `digits`.
    #[allow(dead_code)]
    pub(crate) fn assign_slice(&mut self, digits: &[Digit], is_negative: bool) {
        self.vec.clear();
        self.vec.extend_from_slice(digits);
        self.neg = is_negative;
        self.trim();
    }
}
