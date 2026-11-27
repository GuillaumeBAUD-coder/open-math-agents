import Mathlib

/-!
# A243890: Primes of the form 2*n^2+38*n+17.

Source: https://oeis.org/A243890
Credit: @cjchaffin

Conjecture (stated on the OEIS page): except 521, `2^a(n) - 1` is not prime; in other words,
these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `p = 2*n^2 + 38*n + 17` with `n ≥ 1`, as in the OEIS programs
  (`Table[..., {n, 800}]` and Magma `n in [1..]`). The value at `n = 0` is `17`, which is prime
  but is not a term: the data begins at the value for a positive `n`.
- The exception `521` is kept as a hypothesis `f n ≠ 521`, so the conjecture says nothing about it (`2^521 - 1` is a Mersenne prime).
-/

namespace OMA.S_oeis_a243890

/-- The quadratic `2*n^2 + 38*n + 17`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 38 * n + 17

theorem main : ∀ n : ℕ, 1 ≤ n → (f n).Prime → f n ≠ 521 → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a243890
