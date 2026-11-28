import OMAReductions.R_FibonacciPrimes_fib_primes_infinite_variant_R1
import Mathlib

theorem OMA.solution : OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1.H2 := by
  intro b
  rcases Nat.lt_or_ge b 5 with h | h
  · interval_cases b <;> decide
  · exact (Nat.le_fib_self h).trans (Nat.le_succ _)
