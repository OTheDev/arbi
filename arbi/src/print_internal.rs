/*
Copyright 2024 Owain Davies
SPDX-License-Identifier: Apache-2.0 OR MIT
*/

use crate::{Arbi, Digit};
use alloc::string::String;
use core::fmt::Write;

impl Arbi {
    /// Prints the integer in the form
    ///
    /// ```text
    /// (d_p * 2**(Digit::BITS * p) + ... + d_0 * 2**(Digit::BITS * 0))
    /// ```
    ///
    /// followed by a newline.
    ///
    /// If the integer is negative, the output will be preceded by a minus sign
    /// (`-`).
    ///
    /// Useful for understanding the internal representation of the integer.
    ///
    /// ## Complexity
    /// \\( O(n) \\)
    #[allow(dead_code)]
    fn to_string_internal(&self) -> String {
        let mut result = String::new();

        if self.size() == 0 {
            writeln!(result, "0 * 2**({} * 0)", Digit::BITS).unwrap();
            return result;
        }

        if self.is_negative() {
            result.push('-');
        }

        let last_index = self.size() - 1;
        write!(
            result,
            "({} * 2**({} * {})",
            self.vec[last_index],
            Digit::BITS,
            last_index
        )
        .unwrap();

        for i in (0..last_index).rev() {
            write!(result, " + {} * 2**({} * {})", self.vec[i], Digit::BITS, i)
                .unwrap();
        }

        write!(result, ")").unwrap();

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DDigit;

    #[test]
    fn print_test() {
        let s = Arbi::from(Digit::MAX).to_string_internal();
        assert_eq!(s, "(4294967295 * 2**(32 * 0))");

        let s = Arbi::from(DDigit::MAX).to_string_internal();
        assert_eq!(s, "(4294967295 * 2**(32 * 1) + 4294967295 * 2**(32 * 0))");
    }
}
