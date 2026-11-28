import OMAStatements.S_oeis_a267826

-- Reduction oeis-a267826.R1 of oeis-a267826: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a267826_R1

open OMA.S_oeis_a267826

/-- Step H1 of the reduction. -/
def H1 : Prop := {n : ℕ | ¬ Rep n}.ncard = 122

/-- Step H2 of the reduction. -/
def H2 : Prop := ¬ Rep 41405

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 41405 < n → Rep n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a267826.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a267826_R1
