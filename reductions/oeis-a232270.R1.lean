import OMAStatements.S_oeis_a232270

-- Reduction oeis-a232270.R1 of oeis-a232270: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a232270_R1

open OMA.S_oeis_a232270

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | a n = 1} = {2, 3, 4, 29, 70, 105}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a232270.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a232270_R1
