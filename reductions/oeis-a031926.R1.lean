import OMAStatements.S_oeis_a031926

-- Reduction oeis-a031926.R1 of oeis-a031926: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a031926_R1

open OMA.S_oeis_a031926

/-- Step H1 of the reduction. -/
def H1 : Prop := {p : ℕ | P p}.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a031926.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a031926_R1
