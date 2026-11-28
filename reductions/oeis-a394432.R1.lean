import OMAStatements.S_oeis_a394432

-- Reduction oeis-a394432.R1 of oeis-a394432: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a394432_R1

open OMA.S_oeis_a394432

/-- Step H1 of the reduction. -/
def H1 : Prop := OddPrimePowers

/-- Step H2 of the reduction. -/
def H2 : Prop := FurtherPower

/-- Step H3 of the reduction. -/
def H3 : Prop := StrictAtPowersOfTwo

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a394432.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a394432_R1
