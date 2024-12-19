[![Test](https://github.com/OTheDev/arbi/actions/workflows/test.yml/badge.svg)](https://github.com/OTheDev/arbi/actions/workflows/test.yml)
[![Static Analysis](https://github.com/OTheDev/arbi/actions/workflows/static.yml/badge.svg)](https://github.com/OTheDev/arbi/actions/workflows/static.yml)
[![github](https://img.shields.io/badge/GitHub-OTheDev/arbi-4467C4?logo=github&labelColor=24292e)](https://github.com/OTheDev/arbi)
[![docs.rs](https://img.shields.io/docsrs/arbi?color=4467C4&labelColor=24292e&label=Docs)](https://docs.rs/arbi/latest/arbi/)
![Crates.io License](https://img.shields.io/crates/l/arbi?color=4467C4&labelColor=24292e&label=License)
[![crates.io](https://img.shields.io/crates/d/arbi?color=4467C4&labelColor=24292e&label=Downloads)](https://crates.io/crates/arbi)

# arbi

`arbi` implements an Arbitrary Precision Integer type: [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html).

## Features

- **No dependencies**.

  Empty dependencies section in `Cargo.toml`.

- **`no_std`**.

  This crate is `no_std` and utilizes the [`alloc`](https://doc.rust-lang.org/1.82.0/alloc/index.html) crate for dynamic memory allocation.

  Enable the `std` feature if you need `std::error::Error` implementations for error types (it is not used for other purposes).

- **`forbid(unsafe_code)`**.

  Statically guarantees that crate code does not use `unsafe` Rust.

- **Pure Rust** implementation.

## Usage

### Construct an `Arbi` integer

The following are equivalent and return an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html)
integer with value `0` (no memory allocation occurs):

- [`Arbi::new()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.new)
- [`Arbi::zero()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.zero)

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

Construct an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer from any primitive integer type value,
any [`f64`](https://doc.rust-lang.org/nightly/core/primitive.f64.html) (except for infinities and NaNs), or any string containing a
base-`base` representation of an integer, where `base` must be in [2, 36].

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

Use [`Arbi::with_capacity_bits()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.with_capacity_bits) or [`Arbi::with_capacity()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.with_capacity) to construct an
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

### Assign to an `Arbi` integer

[`Assign`](https://docs.rs/arbi/latest/arbi/trait.Assign.html) to an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) any primitive integer type value, a floating-point
value, a string, or another [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer.

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

### Comparisons

Compare an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) to another [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html), a primitive integer type value, or a
floating-point value.

All equality and comparison operators are supported `==`, `!=`, `<`, `<=`, `>`,
`>=`.

Comparisons with floating-point values are designed to be consistent with IEEE
754. See[`PartialOrd<f64> for Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#impl-PartialOrd%3Cf64%3E-for-Arbi) for a description of the semantics of
comparing an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) to a floating-point value.

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

### To and From a String

In what follows, `base` must be an integer in `[2, 36]`. Moreover, the
`*_radix()` and `*_base()` string-related functions are equivalent, except that
`*_radix()` functions panic on an invalid base and `*_base()` functions cannot
panic due to an invalid base.

Convert any [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer to a [`String`](https://doc.rust-lang.org/nightly/alloc/string/struct.String.html) containing the base-`base`
representation of the integer.
 - [`Arbi::to_string_radix()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.to_string_radix)
 - [`Arbi::to_string_base()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.to_string_base)
 - `Arbi::to_string()` (uses `Arbi::to_string_base()`, assuming base `10`).

Convert any string containing the base-`base` representation of an integer to
an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html).
 - [`Arbi::from_str_radix()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.from_str_radix)
 - [`Arbi::from_str_base()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.from_str_base)
 - `Arbi::from_str()` (same as `from_str_base()` but assumes base `10` and
   needs `core::str::FromStr` in scope).

Assign any string containing the base-`base` representation of an integer to
an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html).
 - [`Arbi::assign_str_radix()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.assign_str_radix)
 - [`Arbi::assign_str_base()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.assign_str_base)

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

### Arithmetic

All standard arithmetic operations are implemented:
- Binary operators: `+`, `-`, `*`, `/`, `%`, `+=`, `-=`, `*=`, `/=`, `%=`
- Unary operators: `-`.

### Bitwise Operations

All standard bitwise operations are implemented. These operators perform bitwise
operations on integers using two's complement representation (with sign
extension).
- Shift operators: `<<`, `>>`, `<<=`, `>>=`.
- Bitwise complement: `!`.
- Bitwise AND, OR, and XOR: `&`, `|`, `^`, `&=`, `|=`, `^=`.

Test or set a bit at a specified index (zero-based) on the absolute value of an
[`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer:
- [`Arbi::test_bit()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.test_bit)
- [`Arbi::set_bit()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.set_bit)

Obtain the number of bits needed to represent the absolute value of an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html)
integer using [`Arbi::size_bits()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.size_bits):

```rust
use arbi::Arbi;

let mut a = Arbi::zero();
assert_eq!(a.size_bits(), 0);

a.incr(); // 1
assert_eq!(a.size_bits(), 1);
a.incr(); // 10
assert_eq!(a.size_bits(), 2);
a.incr(); // 11
assert_eq!(a.size_bits(), 2);
```

### To Built-In Integer

In what follows, let `*` denote any primitive integer type name:
`i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize`.

Methods
- `wrapping_to_*()`: convert this [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer to a primitive integer type value.
  This is “wrapping”.
  
  See [`Arbi::wrapping_to_i32()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.wrapping_to_i32).

- `checked_to_*()`: try to convert this [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer to a primitive integer
  type value. If this [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer does not fit in the target primitive
  integer type, returns `None`. 
  
  See [`Arbi::checked_to_i32()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.checked_to_i32).

- `fits_*()`: test if this [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer fits in a primitive integer type.
  The [`Fits`](https://docs.rs/arbi/latest/arbi/trait.Fits.html) trait can also be used to do the same thing.
  
  See [`Arbi::fits_i32()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.fits_i32) and also the [`Fits`](https://docs.rs/arbi/latest/arbi/trait.Fits.html) trait.

### To Floating-Point Value

Convert an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer to a floating-point value using the [`Arbi::to_f64()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.to_f64)
method:

```rust
use arbi::{Arbi, Pow};

let a = Arbi::from(-987654321);
assert_eq!(a.to_f64(), -987654321.0);

let b = Arbi::from(1_u64 << 32);
assert_ne!((&b).pow(31_usize).to_f64(), f64::INFINITY);
assert_eq!((&b).pow(32_usize).to_f64(), f64::INFINITY);
```

### Increment/Decrement

Increment or decrement an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer in-place by one using the
[`Arbi::incr()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.incr) and [`Arbi::decr()`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html#method.decr) methods (`+=` and `-=` can also be used).

```rust
use arbi::Arbi;

let mut a = Arbi::zero();

a.incr();
assert_eq!(a, 1);

a.decr();
assert_eq!(a, 0);

a.decr();
assert_eq!(a, -1);
```

### Exponentiation

Raise an [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer to the power of a [`usize`](https://doc.rust-lang.org/nightly/core/primitive.usize.html), [`u128`](https://doc.rust-lang.org/nightly/core/primitive.u128.html), or another
[`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer using the [`Pow`](https://docs.rs/arbi/latest/arbi/trait.Pow.html) trait.

```rust
use arbi::{Arbi, Pow};

let mut a = Arbi::from(2);
a = a.pow(128_usize);
assert_eq!(
    a,
    Arbi::from_str_radix("100000000000000000000000000000000", 16).unwrap()
);
```

### Display

The [`core::fmt::Display`](https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html) implementation uses the base-10 representation of the
[`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html) integer and by extension, so does `Arbi::to_string()`.

```rust
use arbi::Arbi;

let a = Arbi::from(12345);
assert_eq!(format!("{}", a), "12345");
assert_eq!(a.to_string(), "12345");
```

## License

This project is dual-licensed under either the [Apache License, Version 2.0](https://github.com/OTheDev/arbi/blob/main/LICENSE-APACHE)
or the [MIT License](https://github.com/OTheDev/arbi/blob/main/LICENSE-MIT),
at your option.

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this project by you shall be dual-licensed as above, without
any additional terms or conditions.
