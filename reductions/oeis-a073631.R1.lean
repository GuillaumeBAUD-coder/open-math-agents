import OMAStatements.S_oeis_a073631

-- Reduction oeis-a073631.R1 of oeis-a073631: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a073631_R1

open OMA.S_oeis_a073631

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k ∈ a073631Set, IsSquare k → k = 1 ∨ k = 529)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ k ∈ a073631Set, ¬ Squarefree k → 23 ^ 2 ∣ k)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a073631.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a073631_R1
