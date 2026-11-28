import OMAStatements.S_oeis_a293833

-- Reduction oeis-a293833.R1 of oeis-a293833: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a293833_R1

open OMA.S_oeis_a293833

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < n → 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → (a n = 1 → n = 12)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a293833.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a293833_R1
