import OMAStatements.S_oeis_a261295

-- Reduction oeis-a261295.R1 of oeis-a261295: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a261295_R1

open OMA.S_oeis_a261295

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ r : ℚ, 0 < r → ∃ m ∈ S, ∃ n ∈ S, r = (m : ℚ) / n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ r : ℚ, 0 < r → ∃ m ∈ T, ∃ n ∈ T, r = (m : ℚ) / n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a261295.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a261295_R1
