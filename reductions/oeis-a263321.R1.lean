import OMAStatements.S_oeis_a263321

-- Reduction oeis-a263321.R1 of oeis-a263321: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a263321_R1

open OMA.S_oeis_a263321

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → a n ≤ n ^ 2

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → (Even (a n) ↔ n = 7)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a263321.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a263321_R1
