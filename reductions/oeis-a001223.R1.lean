import OMAStatements.S_oeis_a001223

-- Reduction oeis-a001223.R1 of oeis-a001223: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a001223_R1

open OMA.S_oeis_a001223

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ x y : ℕ, 0 < x → 0 < y → ∃ k : ℕ, x * gap (k + 1) = y * gap k)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ x y j : ℕ, 0 < x → 0 < y → 0 < j → ∃ k : ℕ, x * gap (k + j) = y * gap k)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001223.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a001223_R1
