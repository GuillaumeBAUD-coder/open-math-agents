import OMAStatements.S_oeis_a267794

-- Reduction oeis-a267794.R1 of oeis-a267794: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a267794_R1

open OMA.S_oeis_a267794

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ k : ℕ, 1 ≤ k → (∃ j : ℕ, 0 < s k j ∧ (∀ t : ℕ, 1 ≤ t → t ≤ k → s k (j + t) = 0) ∧
          0 < s k (j + k + 1))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 1 ≤ k → (∀ j : ℕ, 0 < s k j → ∃ t : ℕ, 1 ≤ t ∧ t ≤ k + 1 ∧ s k (j + t) ≠ 0)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a267794.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a267794_R1
