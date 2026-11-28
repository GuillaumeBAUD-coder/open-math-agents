import OMAStatements.S_oeis_a098699

-- Reduction oeis-a098699.R1 of oeis-a098699: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a098699_R1

open OMA.S_oeis_a098699

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → 0 < a (2 * k)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 2 ≤ k → a (2 * k) ≤ k ^ 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a098699.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a098699_R1
