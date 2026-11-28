import OMAStatements.S_oeis_a234569

-- Reduction oeis-a234569.R1 of oeis-a234569: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a234569_R1

open OMA.S_oeis_a234569

/-- Step H1 of the reduction. -/
def H1 : Prop := S.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 5 < n → a (n + 1) < a n + a (n - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234569.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a234569_R1
