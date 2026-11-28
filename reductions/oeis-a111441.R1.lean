import OMAStatements.S_oeis_a111441

-- Reduction oeis-a111441.R1 of oeis-a111441: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a111441_R1

open OMA.S_oeis_a111441

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, IsTerm 2 k → k % 12 ≠ 3 ∧ k % 12 ≠ 9)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ m : ℕ, 0 < m → Even m → ∀ k : ℕ, IsTerm m k → k % 12 ≠ 3 ∧ k % 12 ≠ 9)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a111441.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a111441_R1
