import OMAStatements.S_oeis_a297293

-- Reduction oeis-a297293.R1 of oeis-a297293: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a297293_R1

open OMA.S_oeis_a297293

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, (0 ≤ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ∧ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ≤ 5)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, (0 ≤ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ∧ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ≤ 4)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, (0 ≤ (c n : ℤ) - 5 * (n : ℤ) ∧ (c n : ℤ) - 5 * (n : ℤ) ≤ 4)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a297293.main := by
  intro h1 h2 h3 x1
  exact ⟨h1 x1, h2 x1, h3 x1⟩

end OMA.R_oeis_a297293_R1
