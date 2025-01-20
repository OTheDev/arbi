/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{base::BIN, Arbi};
use core::fmt;

/// Format an `Arbi` integer in binary (base-2).
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let mut a = Arbi::from(0xC0FFEE);
/// assert_eq!(format!("{a:b}"), "110000001111111111101110");
/// assert_eq!(format!("{a:#b}"), "0b110000001111111111101110");
/// a.negate_mut();
/// assert_eq!(format!("{a:b}"), "-110000001111111111101110");
/// assert_eq!(format!("{a:#b}"), "-0b110000001111111111101110");
///
/// let zero = Arbi::zero();
/// assert_eq!(format!("{zero:b}"), "0");
/// assert_eq!(format!("{zero:#b}"), "0b0");
/// ```
impl fmt::Binary for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, BIN, "0b", true)
    }
}
