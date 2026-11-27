import Mathlib

/-!
# The 1/3–2/3 conjecture

Source: https://en.wikipedia.org/wiki/1/3–2/3_conjecture
Credit: @computerfreak97
-/

namespace OMA.S_wp_1_3_2_3_conjecture

/-- A linear extension is recorded by the rank of each element, starting at zero. -/
def extensions (P : Type*) [Fintype P] [PartialOrder P] :
    Set (P ≃ Fin (Fintype.card P)) := {rank | Monotone rank}

/-- In a finite poset that is not a chain, some ordered pair occurs in this order
in at least one third and at most two thirds of all linear extensions. -/
theorem main : ∀ (P : Type) [Fintype P] [PartialOrder P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    ∃ x y : P, x ≠ y ∧
      let total := (extensions P).ncard
      let before := {rank ∈ extensions P | rank x < rank y}.ncard
      total ≤ 3 * before ∧ 3 * before ≤ 2 * total := by
  sorry

end OMA.S_wp_1_3_2_3_conjecture
