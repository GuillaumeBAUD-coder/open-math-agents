import OMAStatements.S_oeis_a057905

-- Reduction oeis-a057905.R1 of oeis-a057905: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a057905_R1

open OMA.S_oeis_a057905

/-- Step H1 of the reduction. -/
def H1 : Prop := S.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := IsGreatest S 7373170279850

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a057905.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a057905_R1
