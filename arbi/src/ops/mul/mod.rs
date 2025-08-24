/*
Copyright 2025 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

mod arbi_x_arbi;
mod arbi_x_int;
pub(crate) mod impls;
pub(crate) mod square;
#[cfg(test)]
mod test;

/*

TODO: these can be better tuned.

*/
pub(crate) const MUL_KARATSUBA_CUTOFF: usize = 20;
pub(crate) const MUL_TOOMCOOK3_CUTOFF: usize = 220;
pub(crate) const MUL_SQUARE_KARATSUBA_CUTOFF: usize = 40;
pub(crate) const MUL_SQUARE_TOOMCOOK3_CUTOFF: usize = 220;

fn scratch_size(n: usize) -> usize {
    if n <= MUL_KARATSUBA_CUTOFF {
        // Gradeschool
        0
    } else if n <= MUL_TOOMCOOK3_CUTOFF {
        // Karatsuba
        2 * n + 12
    } else {
        // Toom-Cook 3-way
        4 * n
    }
}

fn square_scratch_size(n: usize) -> usize {
    if n <= MUL_SQUARE_KARATSUBA_CUTOFF {
        // Algorithm 14.16 from Handbook of Applied Cryptography (1996)
        0
    } else if n <= MUL_SQUARE_TOOMCOOK3_CUTOFF {
        // Karatsuba
        2 * n + 12
    } else {
        // Toom-Cook 3-way
        4 * n
    }
}
