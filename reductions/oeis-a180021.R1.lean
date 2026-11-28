import OMAStatements.S_oeis_a180021

-- Reduction oeis-a180021.R1 of oeis-a180021: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a180021_R1

open OMA.S_oeis_a180021

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ k : ℕ, 0 ≤ secondDifference k

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, secondDifference k ≤ 3

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a180021.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a180021_R1
