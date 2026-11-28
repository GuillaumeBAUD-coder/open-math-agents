import OMAStatements.S_oeis_a001954

-- Reduction oeis-a001954.R1 of oeis-a001954: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a001954_R1

open OMA.S_oeis_a001954
open Real

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → 1 / (n : ℝ) ^ 2 < s (a n - 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001954.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a001954_R1
