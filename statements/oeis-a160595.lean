import Mathlib

/-!
# A160595: Numerator of resilience R(n) = phi(n)/(n-1), with a(1) = 1 by convention.

Source: https://oeis.org/A160595
Credit: @divmxnd0x

Conjecture (Thomas Ordowski, Mar 13 2019, stated in A160595): `a(n) > 2` for every composite
`n > 6` (slightly stronger than Lehmer's totient conjecture).

Formalization notes:
* For `n ≥ 2`, `a n` is the numerator of the reduced fraction `phi(n)/(n-1)` (`Rat.num`).
-/

namespace OMA.S_oeis_a160595

/-- A160595(n) for `n ≥ 2`: the numerator of `phi(n)/(n - 1)`. -/
def a (n : ℕ) : ℤ := ((Nat.totient n : ℚ) / ((n : ℚ) - 1)).num

/-- Ordowski's conjecture: `a(n) > 2` for every composite `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → ¬ n.Prime → 2 < a n := by
  sorry

end OMA.S_oeis_a160595
