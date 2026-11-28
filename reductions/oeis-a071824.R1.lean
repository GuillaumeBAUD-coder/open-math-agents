import OMAStatements.S_oeis_a071824

-- Reduction oeis-a071824.R1 of oeis-a071824: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a071824_R1

open OMA.S_oeis_a071824

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, n > 1000 → (aSeq n : ℝ) - (n : ℝ) / 2 < -Real.sqrt (n : ℝ)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, n > 1000 → (bSeq n : ℝ) - (n : ℝ) / 2 > Real.sqrt (n : ℝ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a071824.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a071824_R1
