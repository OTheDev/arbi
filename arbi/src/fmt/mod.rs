/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{base::Base, Arbi};
use core::fmt;

mod binary;
mod display;
mod hex;
mod octal;

impl Arbi {
    /// Helper for the implementations of `core::fmt`'s `LowerHex`, `UpperHex`,
    /// `Octal`, and `Binary` traits.
    fn fmt_base(
        &self,
        f: &mut fmt::Formatter<'_>,
        base: Base,
        prefix: &str,
        lowercase: bool,
    ) -> fmt::Result {
        let string = self.to_string_base_(base, lowercase);
        if let Some(s) = string.strip_prefix('-') {
            f.pad_integral(false, prefix, s)
        } else {
            f.pad_integral(true, prefix, &string)
        }
    }
}
