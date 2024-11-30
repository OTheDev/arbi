/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::assign::Assign;
use crate::Arbi;

/// Construct an [`Arbi`] integer from a floating-point value.
///
/// # Panic
/// Panics when attempting to convert a `NaN` or infinity.
///
/// # Note
/// In Rust, when [casting a primitive float to a primitive integer type](
/// https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions),
/// `NaN`s are converted to `0` and values with large magnitudes and infinities
/// are saturated to the maximum and minimum values of the integer type.
///
/// In contrast, this function panics when `NaN` or infinity is encountered.
///
/// Otherwise, the semantics of this function are consistent with Rust's
/// built-in behavior for casting floats to integers.
///
/// # Examples
/// ```
/// use arbi::Arbi;
///
/// let a = Arbi::from(12345.6789);
/// assert_eq!(a, 12345);
/// assert_eq!(a, 12345.6789 as i32)
/// ```
///
/// Attempting to convert infinity panics.
///
/// ```should_panic
/// use arbi::Arbi;
///
/// let a = Arbi::from(f64::INFINITY);
/// ```
///
/// Attempting to convert `NaN` panics.
///
/// ```should_panic
/// use arbi::Arbi;
///
/// let b = Arbi::from(f64::NAN);
/// ```
///
/// ## Complexity
/// \\( O(1) \\)
impl From<f64> for Arbi {
    fn from(value: f64) -> Self {
        let mut ret = Arbi::new();
        ret.assign(value);
        ret
    }
}
