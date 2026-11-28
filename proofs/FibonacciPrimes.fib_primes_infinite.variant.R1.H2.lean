import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_variant_R1

/-!
# Step H2 of `FibonacciPrimes.fib_primes_infinite.variant`: `b ≤ fib b + 1`

The Fibonacci sequence grows at least linearly along the indices: from `b ≥ 5` on,
`fib b = fib (b - 1) + fib (b - 2) ≥ (b - 2) + (b - 3) = 2 b - 5 ≥ b`, and the first five values
check directly. Mathlib packages this as `Nat.le_fib_add_one`. -/

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1.H2 :=
  Nat.le_fib_add_one
