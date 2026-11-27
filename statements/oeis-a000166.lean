import Mathlib

/-!
# Derangements and perfect powers

Source: https://oeis.org/A000166
Credit: @Ciphore

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a000166

/-- The `n`th derangement number: the number of permutations of an `n`-element set with no
fixed point. -/
noncomputable def derangementCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ≠ i).card

/-- The OEIS conjecture: for `n > 2`, the only derangement number that is a perfect power is
`a(4) = 3²`. -/
theorem main : ∀ n : ℕ, 2 < n →
    (∃ a e : ℕ, 2 ≤ e ∧ derangementCount n = a ^ e) →
    n = 4 ∧ derangementCount n = 3 ^ 2 := by
  sorry

end OMA.S_oeis_a000166
