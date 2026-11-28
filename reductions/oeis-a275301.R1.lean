import OMAStatements.S_oeis_a275301

-- Reduction oeis-a275301.R1 of oeis-a275301: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a275301_R1

open OMA.S_oeis_a275301

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, (a n = 1 →
      n ∈ ({0, 5, 6, 7, 8, 11, 14, 15, 30, 78, 90, 93, 106, 111, 117, 125, 223, 335} : Finset ℕ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a275301.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a275301_R1
