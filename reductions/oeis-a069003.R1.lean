import OMAStatements.S_oeis_a069003

-- Reduction oeis-a069003.R1 of oeis-a069003: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a069003_R1

open OMA.S_oeis_a069003

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (∃ d : ℕ, Nat.Prime (n ^ 2 + d ^ 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ 4 * Real.sqrt ((n + 1 : ℝ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a069003.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a069003_R1
