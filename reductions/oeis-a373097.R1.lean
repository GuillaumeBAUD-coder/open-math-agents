import OMAStatements.S_oeis_a373097

-- Reduction oeis-a373097.R1 of oeis-a373097: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a373097_R1

open OMA.S_oeis_a373097

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ a (n+1) = a n + 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ B : ℕ, ∃ n : ℕ, a n + B < a (n+1))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a373097.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a373097_R1
