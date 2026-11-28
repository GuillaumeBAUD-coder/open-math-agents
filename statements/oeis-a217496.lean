import Mathlib

/-!
# A217496: Primes of the form 2*n^2 + 50*n + 23.

Source: https://oeis.org/A217496
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime; in other words, these primes are included in A054723.

Conventions:
- The terms `a(n)` are the primes `2*n^2 + 50*n + 23` with `n ≥ 0`, as in the OEIS programs
  (`n` runs from 0); the first term `23` is the value at `n = 0`.
- Integer `n < 0` gives no new primes: the polynomial is unchanged by `n ↦ -25 - n`, and for
  `-25 < n < 0` its value is negative.
-/

namespace OMA.S_oeis_a217496

/-- The quadratic `2*n^2 + 50*n + 23`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 50 * n + 23

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217496
