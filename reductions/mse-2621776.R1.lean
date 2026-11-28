import OMAStatements.S_mse_2621776

-- Reduction mse-2621776.R1 of mse-2621776: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mse_2621776_R1

open OMA.S_mse_2621776

/-- Step H1 of the reduction. -/
def H1 : Prop := {n : ℕ | Odd (a n)}.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | Even (a n)}.Infinite

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_mse_2621776.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mse_2621776_R1
