import Mathlib

/-!
# OEIS A074766: a(n) = prime(2n) - 2*prime(n) - n.

Source: https://oeis.org/A074766
Credit: @unserus

OEIS: "Conjecture: p(2n) - 2p(n) < 2n for all n."
OEIS indexes primes from 1 (`p(1) = 2`), with offset `n ≥ 1`; here `p(n) = Nat.nth Nat.Prime (n - 1)`.
The difference `p(2n) - 2p(n)` can be negative (e.g. `n = 1`: `3 - 4`), so it is computed in `ℤ`.
-/

namespace OMA.S_oeis_a074766

/-- The `n`-th prime, 1-indexed as in OEIS: `p 1 = 2`, `p 2 = 3`, ... -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- For every `n ≥ 1`, `p(2n) - 2 p(n) < 2n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (p (2 * n) : ℤ) - 2 * p n < 2 * n := by
  sorry

end OMA.S_oeis_a074766
