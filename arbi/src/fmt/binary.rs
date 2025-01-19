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
/// let mut a = Arbi::from(0xC0FFEE);
///
/// assert_eq!(format!("{:b}", a), "110000001111111111101110");
/// assert_eq!(format!("{:#b}", a), "0b110000001111111111101110");
///
/// a.negate_mut();
///
/// assert_eq!(format!("{:b}", a), "-110000001111111111101110");
/// assert_eq!(format!("{:#b}", a), "-0b110000001111111111101110");
/// ```
///
/// # Note
/// Unlike primitive signed integers which use two's complement representation,
/// negative `Arbi` integers are formatted with their magnitude and a `-` prefix
/// (along with `0b` if `#` is specified).
impl fmt::Binary for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, BIN, "0b", true)
    }
}
