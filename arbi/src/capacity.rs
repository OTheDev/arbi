/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, BitCount, Digit};
use alloc::vec::Vec;

impl Arbi {
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
}
