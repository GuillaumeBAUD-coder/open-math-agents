import Mathlib

/-!
# A096380: `(prime(n)+prime(n+1)+prime(n+2)) - prime(n+3)` along consecutive prime 4-tuples.

Source: https://oeis.org/A096380
Credit: @cjchaffin

The first terms are `3, 4, 10, 14, …`, matching the overlapping 4-tuples of successive
primes `(2,3,5,7)`, `(3,5,7,11)`, `(5,7,11,13)`, `(7,11,13,17)`, …

Conjecture (on the OEIS page): there are infinitely many occurrences where the current
term exceeds the next term, i.e. `a(n) > a(n+1)`.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`. The
difference is taken in `ℤ` so the definition does not rely on a natural-number
subtraction.
-/

namespace OMA.S_oeis_a096380

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def a (n : ℕ) : ℤ :=
  (prime n + prime (n + 1) + prime (n + 2) : ℤ) - prime (n + 3)

theorem main : {n : ℕ | 1 ≤ n ∧ a (n + 1) < a n}.Infinite := by
  sorry

end OMA.S_oeis_a096380
