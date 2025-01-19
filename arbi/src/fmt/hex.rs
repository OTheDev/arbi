/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{base::HEX, Arbi};
use core::fmt;

/// Format an `Arbi` integer in lowercase hexadecimal (base-16).
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(0xC0FFEE);
///
/// assert_eq!(format!("{:x}", a), "c0ffee");
/// assert_eq!(format!("{:#x}", a), "0xc0ffee");
///
/// a.negate_mut();
///
/// assert_eq!(format!("{:x}", a), "-c0ffee");
/// assert_eq!(format!("{:#x}", a), "-0xc0ffee");
/// ```
///
/// # Note
/// Unlike primitive signed integers which use two's complement representation,
/// negative `Arbi` integers are formatted with their magnitude and a `-` prefix
/// (along with `0x` if `#` is specified).
impl fmt::LowerHex for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, HEX, "0x", true)
    }
}

/// Format an `Arbi` integer in uppercase hexadecimal (base-16).
///
/// # Examples
/// ```
/// use arbi::Arbi;
/// let mut a = Arbi::from(0xC0FFEE);
///
/// assert_eq!(format!("{:X}", a), "C0FFEE");
/// assert_eq!(format!("{:#X}", a), "0xC0FFEE");
///
/// a.negate_mut();
///
/// assert_eq!(format!("{:X}", a), "-C0FFEE");
/// assert_eq!(format!("{:#X}", a), "-0xC0FFEE");
/// ```
///
/// # Note
/// Unlike primitive signed integers which use two's complement representation,
/// negative `Arbi` integers are formatted with their magnitude and a `-` prefix
/// (along with `0x` if `#` is specified).
impl fmt::UpperHex for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, HEX, "0x", false)
    }
}
