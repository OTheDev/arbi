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
///
/// let mut a = Arbi::from(0xC0FFEE);
/// assert_eq!(format!("{a:x}"), "c0ffee");
/// assert_eq!(format!("{a:#x}"), "0xc0ffee");
/// a.negate_mut();
/// assert_eq!(format!("{a:x}"), "-c0ffee");
/// assert_eq!(format!("{a:#x}"), "-0xc0ffee");
///
/// let zero = Arbi::zero();
/// assert_eq!(format!("{zero:x}"), "0");
/// assert_eq!(format!("{zero:#x}"), "0x0");
/// ```
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
///
/// let mut a = Arbi::from(0xC0FFEE);
/// assert_eq!(format!("{:X}", a), "C0FFEE");
/// assert_eq!(format!("{:#X}", a), "0xC0FFEE");
/// a.negate_mut();
/// assert_eq!(format!("{:X}", a), "-C0FFEE");
/// assert_eq!(format!("{:#X}", a), "-0xC0FFEE");
///
/// let zero = Arbi::zero();
/// assert_eq!(format!("{zero:X}"), "0");
/// assert_eq!(format!("{zero:#X}"), "0x0");
/// ```
impl fmt::UpperHex for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, HEX, "0x", false)
    }
}
