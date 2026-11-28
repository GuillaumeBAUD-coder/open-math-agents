import OMAStatements.S_oeis_a031934

-- Reduction oeis-a031934.R1 of oeis-a031934: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a031934_R1

open OMA.S_oeis_a031934

/-- Step H1 of the reduction. -/
def H1 : Prop := gap16Set.Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n →
        (Nat.nth IsGap16Prime n) ^ n < (Nat.nth IsGap16Prime (n - 1)) ^ (n + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a031934.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a031934_R1
