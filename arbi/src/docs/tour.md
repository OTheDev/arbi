<!---
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# Tour

## Construct

The following are equivalent and return an [`Arbi`] integer with value `0` (no
memory allocation occurs):

- [`Arbi::new()`]
- [`Arbi::zero()`]

`Arbi::default()` also returns zero, but it is not `const`.

```rust
use arbi::Arbi;

let a = Arbi::new();
let b = Arbi::default();
let c = Arbi::zero();

assert_eq!(a, 0);
assert_eq!(a, b);
assert_eq!(b, c);
```

Construct an [`Arbi`] integer from any primitive integer type value, any [`f64`]
(except for infinities and NaNs), or any string containing a base-`base`
representation of an integer, where `base` must be in [2, 36].

```rust
use arbi::{base::DEC, Arbi};

// From any primitive integer type
let a = Arbi::from(u128::MAX);
assert_eq!(a, u128::MAX);

// From any f64 (except for infinities and NaNs)
let b = Arbi::from(f64::MAX);
assert_eq!(b, f64::MAX);

// From a string
let c = Arbi::from_str_radix("123456789", 10).unwrap();
let d = Arbi::from_str_base("123456789", DEC).unwrap();
assert_eq!(c, 123456789);
assert_eq!(c, d);

use core::str::FromStr;

// Currently, FromStr assumes base 10.
let e = Arbi::from_str("-987654321").unwrap();
assert_eq!(e, -987654321);
let f = "123456789".parse::<Arbi>().unwrap();
assert_eq!(f, 123456789);
```

Use [`Arbi::with_capacity_bits()`] or [`Arbi::with_capacity()`] to construct an
integer representing zero with at least a specified capacity:
```rust
use arbi::{Arbi, Assign};

let mut a = Arbi::with_capacity_bits(128);
let initial_capacity = a.capacity_bits();

assert_eq!(a, 0);
assert!(initial_capacity >= 128);

a.assign(u128::MAX);

assert_eq!(a.capacity_bits(), initial_capacity); // no memory allocation needed
assert_eq!(a, u128::MAX);
```

## Assign

[`Assign`] to an [`Arbi`] any primitive integer type value, a floating-point
value, a string, or another [`Arbi`] integer.

The main benefit of assigning is that if there is already enough capacity,
memory allocation need not occur. In contrast, `from` methods typically involve
memory allocation.

```rust
use arbi::{Arbi, Assign};

let mut a = Arbi::with_capacity(10);
let mut capacity = a.capacity();

// From integer
a.assign(u128::MAX);
assert_eq!(a, u128::MAX);
assert_eq!(a.capacity(), capacity); // no memory allocation occurred

// From float
a.assign(f64::MAX);
assert_eq!(a, f64::MAX);
assert!(a.capacity() > capacity); // memory allocation occured because we needed
                                  // more capacity to represent the value
capacity = a.capacity();

// From string (no need for the Assign trait)
if let Err(e) = a.assign_str_radix("123456789", 10) {
    panic!("Parsing error: {}", e);
}
assert_eq!(a, 123456789);
assert_eq!(a.capacity(), capacity); // no memory allocation occurred

// From another Arbi integer
let b = Arbi::from(987654321);
a.assign(&b);
assert_eq!(a.capacity(), capacity); // no memory allocation occurred
```

## Comparisons

Compare an [`Arbi`] to another [`Arbi`], a primitive integer type value, or a
floating-point value.

All equality and comparison operators are supported `==`, `!=`, `<`, `<=`, `>`,
`>=`.

Comparisons with floating-point values are designed to be consistent with IEEE
754. See [`PartialOrd<f64> for Arbi`](Arbi#impl-PartialOrd<f64>-for-Arbi) for a
description of the semantics of comparing an [`Arbi`] to a floating-point value.

```rust
use arbi::{Arbi, Assign};

let mut a;

// Float
a = Arbi::one();
a <<= 2000_usize;

assert_ne!(a, f64::MAX);
assert!(a < f64::INFINITY);
assert!(a > f64::MAX);

// Integer
a.assign(u64::MAX);
assert_eq!(a, u64::MAX);
assert!(u128::MAX > a);
assert!(a > u32::MAX);

// Arbi
let b = Arbi::one();
assert!(a > b);
assert!(b < a);
```

## To and From a String

In what follows, `base` must be an integer in `[2, 36]`. Moreover, the
`*_radix()` and `*_base()` string-related functions are equivalent, except that
`*_radix()` functions panic on an invalid base and `*_base()` functions cannot
panic due to an invalid base.

Convert any [`Arbi`] integer to a [`String`] containing the base-`base`
representation of the integer.
 - [`Arbi::to_string_radix()`]
 - [`Arbi::to_string_base()`]
 - `Arbi::to_string()` (uses `Arbi::to_string_base()`, assuming base `10`).

Convert any string containing the base-`base` representation of an integer to
an [`Arbi`]
 - [`Arbi::from_str_radix()`]
 - [`Arbi::from_str_base()`]
 - `Arbi::from_str()` (same as `from_str_base()` but assumes base `10` and
   needs [`core::str::FromStr`] in scope).

Assign any string containing the base-`base` representation of an integer to
an [`Arbi`].
 - [`Arbi::assign_str_radix()`]
 - [`Arbi::assign_str_base()`]

```rust
use arbi::{base::OCT, Arbi};
use core::str::FromStr; // needed for from_str() alone

let mut a = Arbi::from(u128::MAX);

// To string
assert_eq!(a.to_string(), u128::MAX.to_string()); // assumes base-10
assert_eq!(a.to_string_radix(16), "ffffffffffffffffffffffffffffffff");
assert_eq!(
    a.to_string_base(OCT),
    "3777777777777777777777777777777777777777777"
);

// From string
assert_eq!(
    Arbi::from_str("340282366920938463463374607431768211455").unwrap(),
    u128::MAX
); // assumes base-10
assert_eq!(
    Arbi::from_str_radix("ffffffffffffffffffffffffffffffff", 16).unwrap(),
    u128::MAX
);
assert_eq!(
    Arbi::from_str_base("3777777777777777777777777777777777777777777", OCT)
        .unwrap(),
    u128::MAX
);

// Assign string
a.assign_str_radix("573c0ff2cce44d2025e04db43", 16);
assert_eq!(a, 0x573c0ff2cce44d2025e04db43_u128);

a.assign_str_base("1772555052337322416757226463207030", OCT);
assert_eq!(a, 0o1772555052337322416757226463207030_u128);
```

## Arithmetic

All standard arithmetic operations are implemented:
- Binary operators: `+`, `-`, `*`, `/`, `%`, `+=`, `-=`, `*=`, `/=`, `%=`
- Unary operators: `-`.

## Bitwise Operations

All standard bitwise operations are implemented. These operators perform bitwise
operations on integers using two's complement representation (with sign
extension).
- Shift operators: `<<`, `>>`, `<<=`, `>>=`.
- Bitwise complement: `!`.
- Bitwise AND, OR, and XOR: `&`, `|`, `^`, `&=`, `|=`, `^=`.

Test, set, clear, or invert (i.e. toggle) a bit at a specified index on the
two's complement representation (with sign extension) of an
[`Arbi`] integer:
- [`Arbi::test_bit()`]
- [`Arbi::set_bit()`]
- [`Arbi::clear_bit()`]
- [`Arbi::invert_bit()`]

Obtain the number of bits needed to represent the absolute value of an [`Arbi`]
integer using [`Arbi::size_bits()`]:

```rust
use arbi::Arbi;
let mut a = Arbi::zero();
assert_eq!(a.size_bits(), 0);
a += 1; // 1
assert_eq!(a.size_bits(), 1);
a += 1; // 10
assert_eq!(a.size_bits(), 2);
a += 1; // 11
assert_eq!(a.size_bits(), 2);
```

## To Built-In Integer

In what follows, let `*` denote any primitive integer type name:
`i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize`.

Methods
- `wrapping_to_*()`: convert this [`Arbi`] integer to a primitive integer type value.
  This is “wrapping”.
  
  See [`Arbi::wrapping_to_i32()`].

- `checked_to_*()`: try to convert this [`Arbi`] integer to a primitive integer
  type value. If this [`Arbi`] integer does not fit in the target primitive
  integer type, returns `None`. 
  
  See [`Arbi::checked_to_i32()`].

- `fits_*()`: test if this [`Arbi`] integer fits in a primitive integer type.
  The [`Fits`] trait can also be used to do the same thing.
  
  See [`Arbi::fits_i32()`] and also the [`Fits`] trait.

## To Float

Convert an [`Arbi`] integer to a floating-point value using the [`Arbi::to_f64()`]
method:

```rust
use arbi::{Arbi, Pow};

let a = Arbi::from(-987654321);
assert_eq!(a.to_f64(), -987654321.0);

let b = Arbi::from(1_u64 << 32);
assert_ne!((&b).pow(31_usize).to_f64(), f64::INFINITY);
assert_eq!((&b).pow(32_usize).to_f64(), f64::INFINITY);
```

## Exponentiation

Raise an [`Arbi`] integer to the power of a [`usize`], [`u128`], or another
[`Arbi`] integer using the [`Pow`] trait.

```rust
use arbi::{Arbi, Pow};

let mut a = Arbi::from(2);
a = a.pow(128_usize);
assert_eq!(
    a,
    Arbi::from_str_radix("100000000000000000000000000000000", 16).unwrap()
);
```

## Display

The [`core::fmt::Display`] implementation uses the base-10 representation of the
[`Arbi`] integer and by extension, so does `Arbi::to_string()`.

```rust
use arbi::Arbi;

let a = Arbi::from(12345);
assert_eq!(format!("{}", a), "12345");
assert_eq!(a.to_string(), "12345");
```
