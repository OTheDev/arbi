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
/// let mut a = Arbi::from(12648430);
///
/// assert_eq!(format!("{:o}", a), "60177756");
/// assert_eq!(format!("{:#o}", a), "0o60177756");
///
/// a.negate_mut();
///
/// assert_eq!(format!("{:o}", a), "-60177756");
/// assert_eq!(format!("{:#o}", a), "-0o60177756");
/// ```
///
/// # Note
/// Unlike primitive signed integers which use two's complement representation,
/// negative `Arbi` integers are formatted with their magnitude and a `-` prefix
/// (along with `0o` if `#` is specified).
impl fmt::Octal for Arbi {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_base(f, OCT, "0o", true)
    }
}
