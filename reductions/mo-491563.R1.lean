import OMAStatements.S_mo_491563

-- Reduction mo-491563.R1 of mo-491563: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_mo_491563_R1

open OMA.S_mo_491563
open scoped BigOperators

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n b e : ℕ, 1 < n → 1 < e → centralTrinomial n ≠ b ^ e)

/-- Step H2 of the reduction. -/
def H2 : Prop := qLogConvexTail (weightedTrinomial 2)

/-- Step H3 of the reduction. -/
def H3 : Prop := qLogConvexTail (weightedTrinomial 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_491563.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_mo_491563_R1
