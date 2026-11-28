import OMAStatements.S_oeis_a352305

-- Reduction oeis-a352305.R1 of oeis-a352305: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a352305_R1

open OMA.S_oeis_a352305

/-- Step H1 of the reduction. -/
def H1 : Prop := numWays 188 = 5

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 188 < n → numWays n ≠ 5

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a352305.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a352305_R1
