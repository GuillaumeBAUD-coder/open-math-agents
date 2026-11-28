import OMAStatements.S_oeis_a373616

-- Reduction oeis-a373616.R1 of oeis-a373616: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a373616_R1

open OMA.S_oeis_a373616

/-- Step H1 of the reduction. -/
def H1 : Prop := S.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := IsGreatest S 1612172

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a373616.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a373616_R1
