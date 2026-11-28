import OMAStatements.S_oeis_a006881

-- Reduction oeis-a006881.R1 of oeis-a006881: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a006881_R1

open OMA.S_oeis_a006881

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ p : ℕ, p.Prime → 29 ≤ p → IsSumOfTwo p)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 83 ≤ n → IsSumOfTwo n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006881.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a006881_R1
