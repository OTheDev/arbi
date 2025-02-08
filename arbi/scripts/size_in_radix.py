###############################################################################
# Copyright 2025 Owain Davies
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# This file is part of "arbi", an Arbitrary Precision Integer library for Rust.
###############################################################################

from decimal import getcontext, Decimal, ROUND_CEILING

# Some high enough precision :)
getcontext().prec = 100


# ceil( (log(2) / log(base)) * 2^(digit_bits) )
# Useful for computing the needed capacity for Arbi::to_string()-type functions
def log2_div_logb(base: int, digit_bits: int = 32) -> int:
    x = Decimal(2).ln() / Decimal(base).ln()
    scaled = x * Decimal(1 << digit_bits)

    return int(scaled.to_integral_exact(ROUND_CEILING))


# ceil( (log(base) / log(2^(digit_bits))) * 2^(digit_bits) )
# Useful for computing the needed capacity for Arbi::from_str()-type functions
def logb_div_logab(base: int, digit_bits: int = 32) -> int:
    x = Decimal(base).ln() / Decimal(1 << digit_bits).ln()
    scaled = x * Decimal(1 << digit_bits)

    return int(scaled.to_integral_exact(ROUND_CEILING))


def print_arrays():
    def print_array(prefix: str, digit_bits: int, func, start_base: int):
        print(f"const {prefix}_{digit_bits}: [u{digit_bits}; 37] = [")

        max_hex_digits = digit_bits >> 2
        for base in range(start_base):  # Use 0 for bases [0, start_base)
            print(f"{' ' * 4}0x{'0' * max_hex_digits},")
        for base in range(start_base, 37):
            print(f"{' ' * 4}0x{func(base, digit_bits):x},")

        print("];\n")

    for digit_bits in (32, 64):
        print_array("SCALED_LOG2_DIV_LOG", digit_bits, log2_div_logb, 3)
        print_array("SCALED_LOGB_DIV_LOGAB", digit_bits, logb_div_logab, 2)


if __name__ == "__main__":
    print_arrays()
