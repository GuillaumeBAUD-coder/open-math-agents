import OMAStatements.S_oeis_a085579

-- Reduction oeis-a085579.R1 of oeis-a085579: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a085579_R1

open OMA.S_oeis_a085579

/-- Step H1 of the reduction. -/
def H1 : Prop := Irrational diagonalReal

/-- Step H2 of the reduction. -/
def H2 : Prop := Transcendental ℚ diagonalReal

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085579.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a085579_R1
