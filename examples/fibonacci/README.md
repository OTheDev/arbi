# Fibonacci

In this example, `Arbi` integers are used to implement the function `fib_gte()`,
which returns the first value in the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence)
greater than or equal to its argument.

## Optimization Note

In the implementation, preallocating in the initialization phase helps minimize
memory allocations.
