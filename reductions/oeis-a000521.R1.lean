import OMAStatements.S_oeis_a000521

-- Reduction oeis-a000521.R1 of oeis-a000521: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a000521_R1

open OMA.S_oeis_a000521
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ¬ ∃ (m : ℤ) (k : ℕ), 2 ≤ k ∧ a n = m ^ k)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, (a (n + 2) : ℚ) / a (n + 1) < (a (n + 1) : ℚ) / a n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000521.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a000521_R1
