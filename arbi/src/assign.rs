/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::Arbi;

/// Assign a value of type `T` to an integer.
///
/// One of the main benefits of assigning and reusing an `Arbi` integer is that
/// it can potentially avoid memory allocation if there's already enough
/// capacity. In contrast, `from` methods typically involve memory allocation
/// (when the resulting integer is not zero).
///
/// # Examples
/// ```
/// use arbi::{Arbi, Assign};
///
/// let mut a = Arbi::with_capacity(10);
/// let mut capacity = a.capacity();
///
/// // From integer
/// a.assign(u128::MAX);
/// assert_eq!(a, u128::MAX);
/// assert_eq!(a.capacity(), capacity); // no memory allocation occurred
///
/// // From float
/// a.assign(f64::MAX);
/// assert_eq!(a, f64::MAX);
/// assert!(a.capacity() > capacity); // memory allocation occured because we
///                                   // needed more capacity to represent the
///                                   // value
/// capacity = a.capacity();
///
/// // From string (no need for the Assign trait)
/// if let Err(e) = a.assign_str_radix("123456789", 10) {
///     panic!("Parsing error: {}", e);
/// }
/// assert_eq!(a, 123456789);
/// assert_eq!(a.capacity(), capacity); // no memory allocation occurred
///
/// // From another Arbi integer
/// let b = Arbi::from(987654321);
/// a.assign(&b);
/// assert_eq!(a.capacity(), capacity); // no memory allocation occurred
/// ```
pub trait Assign<T> {
    #[allow(dead_code)]
    fn assign(&mut self, value: T);
}

/// Copies the contents of the argument `Arbi` integer into this `Arbi` integer.
/// If this `Arbi` integer already has enough capacity to represent `value`,
/// then no memory allocation occurs.
impl Assign<&Arbi> for Arbi {
    fn assign(&mut self, value: &Arbi) {
        if self.vec.capacity() < value.size() {
            self.vec.reserve(value.size() - self.vec.capacity());
        }

        self.vec.clear();
        self.vec.extend_from_slice(&value.vec);

        self.neg = value.neg;
    }
}
