/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

macro_rules! for_all_integers {
    ($macro:ident) => {
        $macro!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
    };
}

pub(crate) use for_all_integers;
