import OMAStatements.S_oeis_a091182

-- Reduction oeis-a091182.R1 of oeis-a091182: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a091182_R1

open OMA.S_oeis_a091182

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3120 < n → ∃ x y : ℕ, 0 < y ∧ y ≤ x ∧ n = x + y ∧ primePair 1 x y)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ m : ℕ, 0 < m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even ((m - 1) * n) →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ primePair m x y)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a091182.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a091182_R1
