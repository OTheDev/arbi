/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

// ($($int:ty),*) => {}
macro_rules! for_all_ints {
    ($macro:ident) => {
        $macro!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
    };
}

// ($(($int:ty, $uint:ty, $max_size:expr)),*) => {}
macro_rules! for_all_ints_with_metadata {
    ($macro:ident) => {
        $macro!(
            // ($int:ty, $uint:ty, $max_size:expr)
            // int      : any primitive integer type
            // uint     : unsigned primitive integer type of same width as int
            // max_size : maximum number of base Arbi::BASE digits needed to
            //            represent the maximum value of this type
            (i8, u8, { crate::util::max_digits::<i8>() }),
            (u8, u8, { crate::util::max_digits::<u8>() }),
            (i16, u16, { crate::util::max_digits::<i16>() }),
            (u16, u16, { crate::util::max_digits::<u16>() }),
            (i32, u32, { crate::util::max_digits::<i32>() }),
            (u32, u32, { crate::util::max_digits::<u32>() }),
            (i64, u64, { crate::util::max_digits::<i64>() }),
            (u64, u64, { crate::util::max_digits::<u64>() }),
            (i128, u128, { crate::util::max_digits::<i128>() }),
            (u128, u128, { crate::util::max_digits::<u128>() }),
            (isize, usize, { crate::util::max_digits::<isize>() }),
            (usize, usize, { crate::util::max_digits::<usize>() })
        );
    };
}

pub(crate) use for_all_ints;
pub(crate) use for_all_ints_with_metadata;
