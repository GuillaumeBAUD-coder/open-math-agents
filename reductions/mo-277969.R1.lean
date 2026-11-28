import OMAStatements.S_mo_277969

-- Reduction mo-277969.R1 of mo-277969: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_277969_R1

open OMA.S_mo_277969

/-- Step H1 of the reduction. -/
def H1 : Prop := Summable term

/-- Step H2 of the reduction. -/
def H2 : Prop := Irrational (∑' n : ℕ, term n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mo_277969.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_277969_R1
