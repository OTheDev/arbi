//! Extended documentation.
//!
//! Currently, this only includes notes on some of the algorithms used.

//! # Algorithms

//! ## Addition
//! Knuth Algorithm A (Vol. 2, 4.3.1, p. 266)
//!
//! **Input**:
//! \\[
//!     (u\_{n-1} \cdots u\_{0})\_{b}, (v\_{n-1} \cdots v\_{0})\_{b} \geq 0
//! \\]
//!
//! **Output**: radix-b sum
//! \\[
//!     (w\_{n} \cdots w\_{0})\_{b}, \\; w\_{n} \in \{0, 1\}
//! \\]
//!
//! 1. Set \\( j \leftarrow 0, \\; k \leftarrow 0 \\).
//!
//! 2. Set
//! \\[
//! \begin{align}
//!     t     &\leftarrow u_{j} + v_{j} + k                                     \\\\
//!     w_{j} &\leftarrow t \bmod b                                             \\\\
//!     k     &\leftarrow \left\lfloor \frac{t}{b} \right\rfloor
//!         \Longleftrightarrow k \leftarrow t \geq b
//! \end{align}
//! \\]
//!
//! 3. Increase \\( j \\) by one. If \\( j < n \\), go to (2); else, set \\(
//!     w_{n} \leftarrow k \\) and terminate.
//!
//! The use of the temporary \\( t \\) in (2) permits the same storage locations
//! for both input and output (Exercise 30, p. 283). *This applies for algorithm
//! S as well*.

//! ## Subtraction
//! **Input**:
//! \\[
//!     (u\_{n-1} \cdots u\_{0})\_{b} \geq (v\_{n-1} \cdots v\_{0})\_{b} \geq 0
//! \\]
//!
//! **Output**: radix-b difference
//! \\[
//!     (w\_{n-1} \cdots w\_{0})\_{b}
//! \\]
//!
//! 1. Set \\( j \leftarrow 0, \\; k \leftarrow 0 \\).
//!
//! 2. Set
//! \\[
//! \begin{align}
//!     t     &\leftarrow u\_{j} - v\_{j} + k                                     \\\\
//!     w\_{j} &\leftarrow t \bmod b                                             \\\\
//!     k     &\leftarrow \left\lfloor \frac{t}{b} \right\rfloor
//! \end{align}
//! \\]
//!
//! 3. Increase \\( j \\) by one. If \\( j < n \\), go to (2); else, terminate.

//! ## Multiplication

//! ### Knuth Algorithm M
//! Knuth Algorithm M (Vol. 2, 4.3.1, pp. 268-269)
//!
//! **Input**: \\( (u\_{m-1} \ldots u\_{0})\_{b},
//!                (v\_{n-1} \ldots v\_{0})\_{b} \geq 0 \\)
//!
//! **Output**: radix-b product \\( (w\_{m+n-1} \ldots w\_{0})\_{b} \\)
//!
//! 1. Set \\( w\_{m-1}, \ldots , w\_{0} \\) to 0. Set \\( j \leftarrow 0 \\).
//!
//! 2. Set \\( i \leftarrow 0, k \leftarrow 0 \\).
//!
//! 3. Set (in order from top to bottom)
//! \\[
//! \begin{align}
//!     t          &\leftarrow u\_{i} \times v\_{j} + w\_{i + j} + k             \\\\
//!     w\_{i + j} &\leftarrow t \bmod b                                         \\\\
//!     k          &\leftarrow \left\lfloor \frac{t}{b} \right\rfloor
//! \end{align}
//! \\]
//!
//! 4. Increase \\( i \\) by one. If \\( i < m \\), go to (3); else, set \\(
//!     w\_{j + m} \leftarrow k \\).
//!
//! 5. Increase \\( j \\) by one. If \\( j < n \\), go to (2); else, terminate.
//!
//! Algorithm permits \\( v\_{j} \\) to be in the same memory location as
//! \\( w\_{j + n} \\) (Exercise 30, p. 627) but, in general, special handling is
//! needed for overlapping memory (e.g. through the use of temporaries).

//! ### Multiple-Precision Squaring
//!
//! Knuth Algorithm M can be used generally for multiplying two arbitrary
//! precision integers. However, if the two operands are equal, there are
//! algorithms that can improve the efficiency by about a factor of two. For
//! multiple-precision squaring, we follow **Algorithm 14.16** from the
//! **Handbook of Applied Cryptography** by A. Menezes, P. van Oorschot, and S.
//! Vanstone (pp. 596-597).

//! ### Karatsuba
//!
//! When both operands of multiplication require many base \\( b \\) digits,
//! we can make use of the following observation to implement a recursive
//! algorithm that is more efficient than the standard quadratic
//! pencil-and-paper method.
//!
//! The following is adapted from Knuth Vol. 2, pp. 294-295.
//!
//! Consider two integers with \\( 2n \\) base-b digits and their product:
//! \\[
//! \begin{align}
//!     u &= (u\_{2n-1} \cdots u\_{0})\_{b} = b^{n}U\_{1} + U\_{0} \\\\
//!     v &= (v\_{2n-1} \cdots v\_{0})\_{b} = b^{n}V\_{1} + V\_{0} \\\\
//!     U\_{1} &\equiv (u\_{2n-1} \cdots u\_{n})\_{b},
//!         \\; U\_{0} \equiv (u\_{n-1} \cdots u\_{0})\_{b} \\\\
//!     V\_{1} &\equiv (v\_{2n-1} \cdots v\_{n})\_{b},
//!         \\; V\_{0} \equiv (v\_{n-1} \cdots v\_{0})\_{b} \\\\
//!     uv  &= (b^{n}U\_{1} + U\_{0})(b^{n}V\_{1} + V\_{0})
//! \end{align}
//! \\]
//!
//! It is simple to verify that the product is equivalent to
//!
//! \\[
//!     uv = b^{2n}U\_{1}V\_{1} + b^{n}\left[(U\_{1}+U\_{0})(V\_{1}+V\_{0}) -
//!         (U\_{0}V\_{0} + U\_{1}V\_{1})\right] + U\_{0}V\_{0}
//! \\]
//!
//! The result of multiplying two \\( 2n \\) digit integers can be found
//! via three multiplications of \\( n \\) digit integers (plus cheaper bit
//! shifts and additions).

//! ## Division
//!
//! ### Knuth Algorithm D
//! Knuth Algorithm D (Vol. 2, 4.3.1, pp. 272-273) with Execise 37 (p. 283).
//!
//! **Input**: \\( u = (u\_{m+n-1} \cdots u\_{0})\_{b},
//!                v = (v\_{n-1} \cdots v\_{0})\_{b} \geq 0, \\;
//!                v\_{n-1} \neq 0, \\; n > 1 \\)
//!
//! **Output**: radix-b
//! \\[
//! \begin{align}
//!     \text{quotient}&:
//!         \left\lfloor \frac{u}{v} \right\rfloor = (q\_{m} \cdots q\_{0})\_{b}     \\\\
//!     \text{remainder}&: u \bmod v = (r\_{n-1} \cdots r\_{0})\_{b}
//! \end{align}
//! \\]
//!
//! 1. Normalize. Assuming \\( b \\) is a power of 2, set \\( d \leftarrow 2^{e} \\)
//!     such that \\( b > 2^{e} \times v\_{n-1} \geq \frac{b}{2} \\). Then set
//! \\[
//!     \begin{align}
//!         (u_{m+n} \cdots u_{0})\_{b} &\text{ to } (u\_{m+n-1} \cdots u\_{0})\_{b} \times d \\\\
//!         (v_{n-1} \cdots v_{0})\_{b} &\text{ to } (v\_{n-1} \cdots v\_{0})\_{b} \times d
//!     \end{align}
//! \\]
//!
//!     This can be achieved through bit shifting.
//!
//! 2. Set \\( j \leftarrow m \\).
//!
//! 3. Set
//! \\[
//! \begin{align}
//!     \hat{q} &\leftarrow \left\lfloor \frac{u_{j+n}b + u_{j+n-1}}{v_{n-1}}
//!         \right\rfloor                                                         \\\\
//!     \hat{r} &\leftarrow (u_{j+n}b + u_{j+n-1}) \bmod v_{n-1}
//! \end{align}
//! \\]
//!     Now, if \\( \hat{q} = b \\) or \\( \hat{q}v_{n-2} > b\hat{r} + u_{j+n-2}
//!     \\), then decrease \\( \hat{q} \\) by 1, increase \\( \hat{r} \\) by \\(
//!     v_{n-1} \\) and repeat this test if \\( \hat{r} < b \\).
//!
//! 4. Replace \\( (u\_{j+n} \cdots u\_{j})\_{b} \\) by
//! \\[
//!     (u\_{j+n} \cdots u\_{j})\_{b} - \hat{q}(v\_{n-1} \cdots v\_{0})\_{b}
//! \\]
//!
//!     The digits \\( (u_{j+n},\ldots,u_{j}) \\) should be kept positive. If the
//!     result of this step is actually negative, \\( (u_{j+n} \cdots u_{j})_{b} \\)
//!     should be left as the true value plus \\( b^{n+1} \\), namely, as the \\( b
//!     \\)'s complement of the true value and a borrow to the left should be
//!     remembered.
//!
//! 5. Set \\( q_{j} \leftarrow \hat{q} \\). If the result of (4) was negative,
//!     go to (6); otherwise, go to (7).
//!
//! 6. Decrease \\( q_{j} \\) by 1 and add \\( (0v\_{n-1} \cdots v\_{0})\_{b} \\)
//!     to \\( (u\_{j+n} \cdots u_{j})\_{b} \\). A carry will occur to the left of
//!     \\( u\_{j+n} \\) and it should be ignored.
//!
//! 7. Decrease \\( j \\) by one. Then, if \\( j \geq 0 \\), go to (3).
//!
//! 8. \\( (q\_{m} \cdots q\_{0})\_{b} \\) is the quotient and the remainder is the
//!     result of \\( (u\_{n-1} \cdots u\_{0})\_{b} \\) divided by \\( d \\).

//! ### Binary Long Division
//!
//! **Not used**.
//!
//! Let \\( n \\) denote the number of bits in numerator \\( u \\). Let \\(
//! X(i) \\) denote the \\( ith \\) bit of X (zero-based indexing; zero gives
//! the LSB). This algorithm assumes that \\( u \geq 0, \\; v > 0 \\).
//!
//! 1. Set \\( q \leftarrow 0, \\; r \leftarrow 0 \\).
//! 2. Set \\( i \leftarrow n - 1 \\).
//! 3. Set \\( r \leftarrow r << 1 \\).
//! 4. Set \\( r(0) \leftarrow u(i) \\).
//! 5. If \\( r \geq v \\), set
//! \\[
//! \begin{align}
//!     r    &\leftarrow r - v                                                  \\\\
//!     q(i) &\leftarrow 1
//! \end{align}
//! \\]
//! 6. Decrease \\( i \\) by one. If \\( i \geq 0 \\), go to (3); else,
//!     terminate.

//! ### Division by single-precision integer
//! Knuth Exercise 16 (Vol. 2, 4.3.1, p. 282)
//!
//! **Input**: \\( u = (u\_{n-1} \ldots u\_{0})\_{b} \geq 0 \\; \text{and} \\;
//!                v \in (0, b-1] \\)
//!
//! **Output**: radix-b
//! \\[
//! \begin{align}
//!     \text{quotient}&:
//!         \left\lfloor \frac{u}{v} \right\rfloor = (w\_{n-1} \cdots w\_{0})\_{b}   \\\\
//!     \text{remainder}&: u \bmod v = r
//! \end{align}
//! \\]
//!
//! 1. Set \\( r \leftarrow 0, \\; j \leftarrow n - 1 \\).
//!
//! 2. Set
//! \\[
//! \begin{align}
//!     w_{j} &\leftarrow \left\lfloor \frac{(rb + u\_{j})}{v} \right\rfloor     \\\\
//!     r     &\leftarrow (rb + u\_{j}) \bmod v
//! \end{align}
//! \\]
//!
//! 3. Decrease \\( j \\) by 1. If \\( j \geq 0 \\), go to (2); else, terminate.

//! # String to Integer
//!
//! String to integer conversion algorithms tend to follow a similar structure.
//!
//! Many string to integer conversion functions have an integer `base` argument,
//! accepting a base in \\( [2, 36] \\). The expected string of characters
//! consists of digits and/or letters, together, representing the integer in the
//! provided base. When processing the string of digits, characters '0' to '9'
//! are mapped to the integer values 0 to 9, and the 26 letters in the alphabet,
//! `a` (or `A`) to `z` (or `Z`), are mapped to the values 10 to 35:
//!
//! \\[
//! \begin{align}
//!     a & \mapsto 10   \\\\
//!     b & \mapsto 11   \\\\
//!       & ...          \\\\
//!     z & \mapsto 35
//! \end{align}
//! \\]
//!
//! Suppose we have a string of \\( m \\) characters, \\( (ch\_{m-1}, \ldots,
//! ch\_{0}) \\), where each character represents a digit in some base \\( b \in
//! [2, 36] \\). (Since \\( b > 1 \\), there exists unique coefficients \\(
//! a\_{m-1}, \ldots, a\_{0} \\) such that the integer is equal to \\( a\_{m-1}
//! \cdot b^{m-1} + \cdots + a\_{0} \cdot b^{0}) \\). The resulting integer
//! can be represented as:
//!
//! \\[
//!     (a\_{m-1} \cdots a\_{0})\_{b} = a\_{m-1} \cdot b^{m-1} + \cdots + a\_{0} \cdot
//!                                  b^{0}
//! \\]
//!
//! 1. **Set result to 0**. \\( \text{result} = 0 \\)
//!
//! 2. **Iterate over the characters**. For each character in \\( (ch\_{m-1},
//!     \ldots, ch\_{0}) \\):
//!
//!     (a) **Convert the character to the base b digit it represents**. Call this
//!         value \\( a\_{j} \\), where \\( a\_{j} \in \\{0, 1, ..., b - 1\\} \\). \\(
//!         a\_{j} \\) is the "current digit".
//!     
//!     (b) **Multiply and add**.
//!     \\[
//!         \text{result} = \text{result} \cdot b + a\_{j}
//!     \\]
//!
//! Writing out the value of the result at the end of each iteration:
//!
//! \\[
//! \begin{align}
//!     k = 0&:
//!         \text{result} = a\_{m - 1}                                               \\\\
//!     k = 1&:
//!         \text{result} = a\_{m - 1} \cdot b + a\_{m-2}                            \\\\
//!     k = 2&:
//!         \text{result} = a\_{m - 1} \cdot b^{2} + a\_{m - 2} \cdot b + a\_{m - 3} \\\\
//!     &\ldots                                                                      \\\\
//!     k = m - 1&:
//!         \text{result} = a\_{m - 1} \cdot b^{m - 1} + \cdots + a\_{0} \cdot b^{0}
//! \end{align}
//! \\]
//!
//! It's clear we would be able to prove by induction that this holds generally.
//!
//! Note.
//! Step (2)(a).
//! Characters \\( ch\_{j} \\) in the range ['0', '9'] have values
//! \\[
//!     a\_{j} = ch\_{j} - \text{'0'}
//! \\]
//! The fact that characters corresponding to decimal digits have consecutive
//! integer values is guaranteed by the C/C++ standards. In most systems,
//! lowercase and uppercase letters also have consecutive integer values, but
//! this is not guaranteed by the standards. In systems that do make their
//! values consecutive, we can use the relationships below. However, for
//! maximizing portability, this implementation *does not* assume that their
//! values are consecutive. <br><br>
//! Characters in the range ['a', 'z'] have values
//! \\[
//!     a\_{j} = ch\_{j} - \text{'a'} + 10
//! \\]
//! Characters in the range ['A', 'Z'] have values
//! \\[
//!     a\_{j} = ch\_{j} - \text{'A'} + 10
//! \\]
//!
//! Once we start dealing with many very large strings, analysis and benchmarks
//! show that we can do a lot better by processing the string of alphanumerics
//! in batches.
//!
//! Let \\( e \\) denote the exponent corresponding to the highest power of base
//! \\( b \in [2, 36] \\) that fits in a base \\( \text{base} > b \\) digit.
//!
//! For example, if \\( \text{base} = 2^{64} \\), the highest power of 10 that
//! fits in a base-`base` digit is \\( 10^{19} \\). \\( e \\) is then 19.
//!
//! By definition, any \\( e \\)-digit base-b integer
//!
//! \\[
//!     \phi\_{e - 1}\cdot b^{e - 1} + \cdots + \phi\_{0} \cdot b^{0}
//! \\]
//!
//! can be represented by a single base-`base` digit. The exponent \\( e \\)
//! can be referred to as the **maximum batch size** (i.e. the maximum number of
//! characters in a batch).
//!
//! 1. **Set result to 0**. \\( \text{result} = 0 \\).
//!
//! 2. **Set k to 0**. \\( k = 0 \\). Define \\( k \\) as a zero-based index for
//!     the characters in a string of \\( m \\) alphanumerics. Valid indices are
//!     in the set \\( [0, m - 1] \\).
//!
//! 3. **Iterate over the characters**.
//!
//!     (a) If \\( k \\) is equal to \\( m \\), **return** \\( \text{result} \\).
//!
//!     (b) **Set batch value to 0**. \\( \text{batch_value} = 0 \\).
//!
//!     (c) **Calculate how many characters to batch**: \\( \lambda \\). This
//!         should be the minimum of \\( e \\) and the number of characters
//!         remaining in the string that have not yet been processed.
//!
//!     \\[
//!         \lambda \equiv \min \\{e, \\; m - k\\}
//!     \\]
//!
//!     (d) **Calculate the batch value**. Use the algorithm specified above. That
//!         is, for each \\( j \in (0, 1, \ldots, \lambda - 1) \\), obtain the base-b
//!         digit that the current character maps to (call this \\( \text{cur\_digit}
//!         \\) ), calculate
//!
//!     \\[
//!         \text{batch\_value} = \text{batch\_value} \* b + \text{cur\_digit}
//!     \\]
//!         and then increase \\( k \\) by 1.
//!
//!     At the end of this loop, the batch value represents a \\( \lambda \\) digit
//!     base-b integer or a single base \\( b^{\lambda} \\) digit.
//!
//!     (e) **Multiply and add**.
//!     \\[
//!         \text{result} = \text{result} \cdot b^{\lambda} + \text{batch\_value}
//!     \\]
//!
//! To see that this works, it helps to write out a few iterations.
//!
//! If \\( m \leq e \\), \\( \text{result} = \text{batch\_value} \\) and we are
//! done.
//!
//! If \\( m \gt e \\), there's at least one full batch and some residual. Let's
//! consider this case.
//!
//! After processing the **first substring**:
//!
//! \\[
//! \begin{align}
//!     \text{result}
//!         &= 0 \cdot b^{e} + (a\_{m-1}b^{e-1} + \cdots + a\_{m-e}b^{0})             \\\\
//!         &= a\_{m-1}b^{e-1} + \cdots + a\_{m-e}b^{0}
//! \end{align}
//! \\]
//!
//! Suppose \\( m - k \ge e\\), so that we have another full batch. The result
//! after processing the **second substring** is:
//!
//! \\[
//! \begin{align}
//!     \text{result}
//!         &= (a\_{m-1}b^{e-1} + \cdots + a\_{m-e}b^{0}) \cdot b^{e} +
//!            (a\_{m-e-1}b^{e-1} + \cdots + a\_{m-2e}b^{0})                          \\\\
//!         &= a\_{m-1}b^{2e-1} + \cdots + a\_{m-e}b^{e} + \cdots + a\_{m-2e}b^{0}
//! \end{align}
//! \\]
//!
//! Suppose \\( m - k \ge e\\) a total of \\( \Omega \\) times. After processing
//! the \\( \Omega\text{th} \\) **substring**:
//!
//! \\[
//! \begin{align}
//!     \text{result}
//!         &= a\_{m-1}b^{\Omega e - 1} + \cdots + a\_{m-\Omega e}b^{0}
//! \end{align}
//! \\]
//!
//! Suppose \\( l \equiv m - k < e \\). This will be the last substring. After
//! processing the last substring:
//!
//! \\[
//! \begin{align}
//!     \text{result}
//!         &= (a\_{m-1}b^{\Omega e-1} + \cdots + a\_{m-\Omega e}b^{0})\cdot b^{l} +
//!            (a\_{m - \Omega e - 1}b^{l-1} + \cdots + a\_{0}b^{0})                  \\\\
//!         &= a\_{m-1}b^{(\Omega e +l)-1} + \cdots + a\_{0}b^{0}                     \\\\
//!         &= a\_{m-1}b^{m-1} + \cdots + a\_{0}b^{0}
//! \end{align}
//! \\]
//!
//! Above, \\( \Omega e + l \\) is none other than the number of characters in
//! the string of alphanumerics, which, by definition, is \\( m \\).
