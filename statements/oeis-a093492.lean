import Mathlib

/-!
# OEIS A093492: Unboundedness of divisor symmetry

Source: https://oeis.org/A093492
Conjecture: Charles R. Greathouse IV (2011).
Credit: @jared-jasinski
-/

namespace OMA.S_oeis_a093492

/-- The divisor counts agree at every positive offset through `k`, and the
next offset ends the symmetry. At offset `n` the left argument reaches zero,
so it has no finite divisor count and the symmetry ends there at the latest.
The sequence is indexed by positive integers. -/
def HasDivisorSymmetry (n k : ℕ) : Prop :=
  k < n ∧
    (∀ r : ℕ, 1 ≤ r → r ≤ k →
      (n - r).divisors.card = (n + r).divisors.card) ∧
    (k + 1 = n ∨ (n - (k + 1)).divisors.card ≠ (n + (k + 1)).divisors.card)

/-- For every bound, some term of A093492 exceeds it. -/
theorem main : ∀ bound : ℕ, ∃ n k : ℕ, bound < k ∧ HasDivisorSymmetry n k := by
  sorry

end OMA.S_oeis_a093492
