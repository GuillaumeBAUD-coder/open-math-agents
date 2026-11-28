import OMAStatements.S_oeis_a283965

-- Reduction oeis-a283965.R1 of oeis-a283965: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283965_R1

open OMA.S_oeis_a283965

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → -1 < Real.sqrt 3 * (n : ℝ) - (a n : ℝ)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → Real.sqrt 3 * (n : ℝ) - (a n : ℝ) < 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a283965.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a283965_R1
