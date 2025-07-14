[![Test](https://github.com/OTheDev/arbi/actions/workflows/test.yml/badge.svg)](https://github.com/OTheDev/arbi/actions/workflows/test.yml)
[![Static Analysis](https://github.com/OTheDev/arbi/actions/workflows/static.yml/badge.svg)](https://github.com/OTheDev/arbi/actions/workflows/static.yml)
[![github](https://img.shields.io/badge/GitHub-OTheDev/arbi-4467C4?logo=github&labelColor=24292e)](https://github.com/OTheDev/arbi)
[![docs.rs](https://img.shields.io/docsrs/arbi?color=4467C4&labelColor=24292e&label=Docs)](https://docs.rs/arbi/latest/arbi/)
![Crates.io License](https://img.shields.io/crates/l/arbi?color=4467C4&labelColor=24292e&label=License)
![MSRV](https://img.shields.io/badge/MSRV-1.65-4467C4?logo=rust&labelColor=24292e)
[![crates.io](https://img.shields.io/crates/d/arbi?color=4467C4&labelColor=24292e&label=Downloads)](https://crates.io/crates/arbi)

# arbi

`arbi` implements an Arbitrary Precision Integer type: [`Arbi`](https://docs.rs/arbi/latest/arbi/struct.Arbi.html).

## Features

- **No dependencies** by default.

  If you need to generate random integers, enable the `rand` feature, which
  depends on the [rand](https://docs.rs/rand/latest/rand/) crate.

- **`no_std`**.

  This crate is `no_std` and utilizes the [`alloc`](https://doc.rust-lang.org/1.82.0/alloc/index.html) crate for dynamic memory allocation.

  Enable the `std` feature if you need `std::error::Error` implementations for error types (it is not used for other purposes).

- **`forbid(unsafe_code)`**.

  Statically guarantees that crate code does not use `unsafe` Rust.

- **Pure Rust** implementation.

## License

This project is dual-licensed under either the [Apache License, Version 2.0](https://github.com/OTheDev/arbi/blob/main/LICENSE-APACHE)
or the [MIT License](https://github.com/OTheDev/arbi/blob/main/LICENSE-MIT),
at your option.

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this project by you shall be dual-licensed as above, without
any additional terms or conditions.
