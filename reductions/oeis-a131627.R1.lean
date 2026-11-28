import OMAStatements.S_oeis_a131627

-- Reduction oeis-a131627.R1 of oeis-a131627: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a131627_R1

open OMA.S_oeis_a131627

/-- Step H1 of the reduction. -/
def H1 : Prop := (¬ 1 ∈ Nat.digits 10 (3 ^ 43))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 43 < k → 1 ∈ Nat.digits 10 (3 ^ k)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a131627.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a131627_R1
