import OMAStatements.S_oeis_a003679

-- Reduction oeis-a003679.R1 of oeis-a003679: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a003679_R1

open OMA.S_oeis_a003679

/-- Step H1 of the reduction. -/
def H1 : Prop := NotSum3.ncard = 210

/-- Step H2 of the reduction. -/
def H2 : Prop := NotSum3.Finite

/-- Step H3 of the reduction. -/
def H3 : Prop := 33066 ∈ NotSum3

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n ∈ NotSum3, n ≤ 33066

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a003679.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a003679_R1
