import OMAStatements.S_oeis_a001176

-- Reduction oeis-a001176.R1 of oeis-a001176: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a001176_R1

open OMA.S_oeis_a001176

/-- Step H1 of the reduction. -/
def H1 : Prop := Filter.Tendsto (densityMod40 1 9 1) Filter.atTop (nhds (1 / 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := Filter.Tendsto (densityMod40 1 9 2) Filter.atTop (nhds (2 / 3))

/-- Step H3 of the reduction. -/
def H3 : Prop := Filter.Tendsto (densityMod40 1 9 4) Filter.atTop (nhds (1 / 6))

/-- Step H4 of the reduction. -/
def H4 : Prop := ( Filter.Tendsto (densityMod40 21 29 1) Filter.atTop (nhds (1 / 2)) ∧ Filter.Tendsto (densityMod40 21 29 4) Filter.atTop (nhds (1 / 2)) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a001176.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a001176_R1
