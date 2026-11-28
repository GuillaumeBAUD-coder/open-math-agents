import Mathlib

/-!
# Nonexpansive retracts of a Hilbert space

Source: Christian, https://mathoverflow.net/questions/312279 (CC BY-SA 4.0).
Credit: @connoranderson.

A retraction is represented by a self-map taking values in C and fixing C
pointwise. The nonempty condition includes the case of the empty subset.
-/

namespace OMA.S_mo_312279

theorem main : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (C : Set H),
    (∃ r : H → H, LipschitzWith 1 r ∧ (∀ x, r x ∈ C) ∧ (∀ x ∈ C, r x=x)) ↔
      C.Nonempty ∧ IsClosed C ∧ Convex ℝ C := by
  sorry

end OMA.S_mo_312279
