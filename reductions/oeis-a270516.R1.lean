import OMAStatements.S_oeis_a270516

-- Reduction oeis-a270516.R1 of oeis-a270516: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a270516_R1

open OMA.S_oeis_a270516

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | 1428 < n ∧ a n = 1} =
      {2205, 2259, 3556, 4107, 4337, 5387, 9331, 16561, 22237, 27569, 63947, 78610}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a270516.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a270516_R1
