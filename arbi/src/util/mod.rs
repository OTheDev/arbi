/*
Copyright 2024-2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

pub(crate) mod arbi_like_array;
// pub(crate) mod float;
pub(crate) mod max_digits;
pub(crate) mod mul;
pub(crate) mod radix_info;
/// Utilities for testing.
#[cfg(test)]
pub(crate) mod test;
pub(crate) mod to_digits;
pub(crate) mod view;

pub(crate) use arbi_like_array::{ArbiLikeArray, IntoArbiLikeArray};
pub(crate) use max_digits::max_digits;
#[allow(unused_imports)]
pub(crate) use view::ArbiLikeView;
