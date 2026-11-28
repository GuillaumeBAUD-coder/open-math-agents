import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_variant_R1

/-!
# Fibonacci indices are bounded by their Fibonacci values

Every index `b` satisfies `b ≤ fib b + 1`: the cases `b ≤ 5` are checked directly, and for
`b ≥ 6` the recurrence gives `fib b = fib (b - 1) + fib (b - 2) ≥ (b - 1) + (b - 2)`, which
is already at least `b - 1`. This is Mathlib's `Nat.le_fib_add_one`.
-/

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1.H2 :=
  Nat.le_fib_add_one
