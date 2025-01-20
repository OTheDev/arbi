/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{base::OCT, Arbi};
use core::fmt;

/// Format an `Arbi` integer in octal (base-8).
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let mut a = Arbi::from(0xC0FFEE);
/// assert_eq!(format!("{a:o}"), "60177756");
/// assert_eq!(format!("{a:#o}"), "0o60177756");
/// a.negate_mut();
/// assert_eq!(format!("{a:o}"), "-60177756");
/// assert_eq!(format!("{a:#o}"), "-0o60177756");
///
/// let zero = Arbi::zero();
/// assert_eq!(format!("{zero:o}"), "0");
/// assert_eq!(format!("{zero:#o}"), "0o0");
/// ```
impl fmt::Octal for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, OCT, "0o", true)
    }
}
