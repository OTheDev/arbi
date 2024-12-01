/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

#![doc = include_str!("../README.md")]
#![forbid(unsafe_code)]
#![no_std]
extern crate alloc;

#[allow(unused_imports)]
use alloc::string::String;
use alloc::vec::Vec;

mod add;
mod assign;
mod assign_double;
mod assign_integral;
mod assign_string;
pub mod base;
mod bit_length;
mod bits;
mod bitwise;
mod builtin_int_methods;
mod comparisons;
mod comparisons_double;
mod comparisons_integral;
mod display;
mod division;
#[cfg(not(doctest))]
#[allow(clippy::doc_lazy_continuation)]
pub mod doc;
mod exponentiation;
mod fits;
mod floor;
mod from_double;
mod from_integral;
mod from_string;
mod increment_decrement;
mod is_signed;
mod left_shift;
mod multiplication;
mod print_internal;
mod right_shift;
mod to_double;
mod to_integral;
mod to_string;
mod to_twos_complement;
mod uints;
mod unary_ops;
mod util;

pub use assign::Assign;
pub use base::{Base, BaseError};
pub use exponentiation::Pow; // No PowAssign implementations yet
pub use fits::Fits;
pub use from_string::ParseError;

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
/// - This crate prefers not to panic, unless for good reason.
///
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
    pub const BASE: DDigit = (1 as DDigit) << Digit::BITS;

    /// Maximum capacity for the internal vector of digits.
    ///
    /// [`Vec`] is limited to `isize::MAX` bytes in capacity. A digit has size
    /// in bytes `core::mem::size_of::<Digit>()`. The maximum capacity is
    /// therefore `isize::MAX / core::mem::size_of::<Digit>()`.
    pub const MAX_CAPACITY: usize =
        (isize::MAX as usize) / core::mem::size_of::<Digit>();

    /// Maximum capacity for the internal vector of digits, in terms of bits.
    ///
    /// This represents the number of bits that can be used to represent the
    /// absolute value of the integer when the internal digit vector is at
    /// maximum capacity.
    ///
    /// This is `Arbi::MAX_CAPACITY * Digit::BITS`.
    pub const MAX_BITS: BitCount =
        Self::MAX_CAPACITY as BitCount * Digit::BITS as BitCount;

    /// Default constructor. The integer is initialized to zero and no memory
    /// allocation occurs.
    ///
    /// Note that [`Arbi::new()`], [`Arbi::zero()`], and [`Arbi::default()`] are
    /// all equivalent.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::new();
    /// assert_eq!(zero, 0);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn new() -> Self {
        Self::default()
    }

    /// Equivalent to [`Arbi::new()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero, 0);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn zero() -> Self {
        Self::default()
    }

    /// Construct a new `Arbi` integer with at least the specified capacity, in
    /// terms of [`Digit`]s.
    ///
    /// The integer's value will be `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::with_capacity(10);
    /// assert_eq!(a.capacity(), 10);
    /// assert_eq!(a, 0);
    /// ```
    ///
    /// Panics if the new capacity exceeds `Arbi::MAX_CAPACITY` digits:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::with_capacity(Arbi::MAX_CAPACITY + 1);
    /// ```
    ///
    /// # Panic
    /// Panics if the new capacity exceeds `isize::MAX` bytes (or
    /// `Arbi::MAX_CAPACITY` digits) or if the allocator reports an allocation
    /// failure.
    #[inline(always)]
    pub fn with_capacity(capacity: usize) -> Self {
        Arbi {
            vec: Vec::with_capacity(capacity),
            neg: false,
        }
    }

    /// Construct a new `Arbi` integer with at least the specified capacity, in
    /// terms of bits.
    ///
    /// The integer's value will be `0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount, Digit};
    ///
    /// let a = Arbi::with_capacity_bits(Digit::BITS as BitCount - 1);
    /// assert_eq!(a.capacity(), 1);
    /// assert_eq!(a, 0);
    ///
    /// let a = Arbi::with_capacity_bits(Digit::BITS as BitCount);
    /// assert_eq!(a.capacity(), 1);
    ///
    /// let a = Arbi::with_capacity_bits(Digit::BITS as BitCount + 1);
    /// assert_eq!(a.capacity(), 2);
    /// ```
    ///
    /// Panics if the new capacity in bits exceeds `Arbi::MAX_BITS` bits:
    /// ```should_panic
    /// use arbi::Arbi;
    ///
    /// // Panics with message: "New capacity exceeds `isize::MAX` bytes".
    /// let a = Arbi::with_capacity_bits(Arbi::MAX_BITS + 1);
    /// ```
    ///
    /// Note that, in practice, while the theoretical limit for the capacity
    /// of a `Vec` in bytes is `isize::MAX`, memory allocation failures
    /// typically happen for less.
    ///
    /// # Panic
    /// Panics if the new capacity exceeds `isize::MAX` bytes (or
    /// `Arbi::MAX_BITS` digits) or if the allocator reports an allocation
    /// failure.
    #[inline(always)]
    pub fn with_capacity_bits(capacity: BitCount) -> Self {
        let cap = BitCount::div_ceil(capacity, Digit::BITS as BitCount);
        if cap > Arbi::MAX_CAPACITY as BitCount {
            panic!("New capacity exceeds `isize::MAX` bytes");
        }

        Arbi {
            vec: Vec::with_capacity(cap as usize),
            neg: false,
        }
    }

    /// Returns the total number of elements the internal digit vector can hold
    /// without reallocating.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Assign};
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.capacity(), 0);
    ///
    /// let mut b = Arbi::with_capacity(10);
    /// assert_eq!(b.capacity(), 10);
    ///
    /// b.assign(u64::MAX); // no memory allocation needed
    /// assert_eq!(b, u64::MAX);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Return the total number of bits the current capacity can hold to
    /// represent the absolute value of this integer.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount, Digit};
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.capacity_bits(), 0);
    ///
    /// let a = Arbi::with_capacity_bits(Digit::BITS as BitCount);
    /// assert!(a.capacity_bits() >= Digit::BITS as BitCount);
    /// ```
    ///
    /// ## Complexitys
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn capacity_bits(&self) -> BitCount {
        self.vec.capacity() as BitCount * Digit::BITS as BitCount
    }

    /// Return the number of [`Digit`]s used to represent the absolute value of
    /// this integer.
    ///
    /// Instance represents `0` if and only if `size() == 0`.
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, Digit};
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size(), 0);
    ///
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size(), 1);
    ///
    /// a.incr();
    /// assert_eq!(a.size(), 2);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size(&self) -> usize {
        self.vec.len()
    }

    /// Return the number of bits used to represent the absolute value of this
    /// integer.
    ///
    /// Instance represents `0` if and only if `size_bits() == 0`.
    ///
    /// This is equivalent to [`Arbi::bit_length()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::{Arbi, BitCount, Digit};
    ///
    /// let zero = Arbi::zero();
    /// assert_eq!(zero.size_bits(), 0);
    ///
    /// let mut a = Arbi::from(Digit::MAX);
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount);
    ///
    /// a.incr();
    /// assert_eq!(a.size_bits(), Digit::BITS as BitCount + 1);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn size_bits(&self) -> BitCount {
        self.bit_length()
    }

    /// See [`Arbi::is_negative()`].
    #[inline(always)]
    fn negative(&self) -> bool {
        self.neg
    }

    /// Return `true` if this `Arbi` integer is (strictly) negative, `false`
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let neg = Arbi::from(-1234);
    /// let pos = Arbi::from(1234);
    /// let zer = Arbi::zero();
    ///
    /// assert!(neg.is_negative());
    /// assert!(!pos.is_negative());
    /// assert!(!zer.is_negative());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_negative(&self) -> bool {
        self.neg
    }

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

    /// Return `true` if this integer is odd, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert!(!zero.is_odd());
    ///
    /// let a = Arbi::from(-123456789);
    /// assert!(a.is_odd());
    ///
    /// let b = Arbi::from(-12345678);
    /// assert!(!b.is_odd());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_odd(&self) -> bool {
        if self.size() == 0 {
            false
        } else {
            (self.vec[0] & 1) != 0
        }
    }

    /// Return `true` if this integer is even, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let zero = Arbi::zero();
    /// assert!(zero.is_even());
    ///
    /// let a = Arbi::from(-12345678);
    /// assert!(a.is_even());
    ///
    /// let b = Arbi::from(-123456789);
    /// assert!(!b.is_even());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_even(&self) -> bool {
        !self.is_odd()
    }

    /// Return `true` if this integer is zero, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let a = Arbi::new();
    /// assert!(a.is_zero());
    ///
    /// let b = Arbi::with_capacity(10);
    /// assert!(a.is_zero());
    ///
    /// let c = Arbi::with_capacity_bits(100);
    /// assert!(c.is_zero());
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn is_zero(&self) -> bool {
        self.vec.is_empty()
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

    /// Negates the integer in-place.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let mut pos = Arbi::from(123456789);
    ///
    /// pos.negate();
    /// assert_eq!(pos, -123456789);
    ///
    /// pos.negate();
    /// assert_eq!(pos, 123456789);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn negate(&mut self) {
        if self.size() > 0 {
            self.neg = !self.neg;
        }
    }

    /// Return a new integer representing the absolute value of this integer.
    ///
    /// For in-place negation (\\( O(1) \\) operation), see [`Arbi::negate()`].
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    ///
    /// let neg = Arbi::from(-123456789);
    /// let pos = neg.abs();
    ///
    /// assert_eq!(pos, 123456789);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    #[inline(always)]
    pub fn abs(&self) -> Arbi {
        let mut ret = self.clone();
        if self.neg {
            ret.negate();
        }
        ret
    }

    /// Return an `Ordering` indicating the sign of the number: `Ordering::Less`
    /// for negative, `Ordering::Equal` for zero, `Ordering::Greater` for
    /// positive.
    ///
    /// # Examples
    /// ```
    /// use arbi::Arbi;
    /// use core::cmp::Ordering;
    ///
    /// let neg = Arbi::from(-123456789);
    /// let zer = Arbi::zero();
    /// let pos = Arbi::from(123456789);
    ///
    /// assert_eq!(neg.sign(), Ordering::Less);
    /// assert_eq!(zer.sign(), Ordering::Equal);
    /// assert_eq!(pos.sign(), Ordering::Greater);
    /// ```
    ///
    /// ## Complexity
    /// \\( O(1) \\)
    #[inline(always)]
    pub fn sign(&self) -> core::cmp::Ordering {
        if self.size() == 0 {
            core::cmp::Ordering::Equal
        } else if self.negative() {
            core::cmp::Ordering::Less
        } else {
            core::cmp::Ordering::Greater
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_even_or_odd() {
        let mut arbi: Arbi;

        arbi = Arbi::from(0);
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());

        arbi = Arbi::from(Digit::MAX);
        assert!(arbi.is_odd());
        assert!(!arbi.is_even());

        arbi = Arbi::from(Digit::MAX as DDigit + 1);
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());

        arbi = Arbi::from(-(Digit::MAX as SDDigit));
        assert!(arbi.is_odd());
        assert!(!arbi.is_even());

        arbi.decr();
        assert!(arbi.is_even());
        assert!(!arbi.is_odd());
    }

    #[test]
    fn test_abs() {
        let pos = Arbi::from(123);
        assert_eq!(123, pos.abs());

        let neg = Arbi::from(-123);
        assert_eq!(123, neg.abs());

        let zer = Arbi::from(0);
        assert_eq!(0, zer.abs());
    }

    #[test]
    fn test_negate() {
        let mut a = Arbi::from(123);
        let mut z = Arbi::zero();

        // Zero
        z.negate();
        assert_eq!(z, 0);

        // Positive
        a.negate();
        assert_eq!(a, -123);

        // Negative
        a.negate();
        assert_eq!(a, 123);

        a.negate();
        a.negate();
        assert_eq!(a, 123);
    }

    #[test]
    fn test_default() {
        let a = Arbi::default();
        assert_eq!(a, 0);

        assert_eq!(a.size(), 0);
        assert_eq!(a.negative(), false);
    }
}
