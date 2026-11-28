import OMAStatements.S_oeis_a254631

-- Reduction oeis-a254631.R1 of oeis-a254631: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a254631_R1

open OMA.S_oeis_a254631

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 35 < n → 1 < a n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a254631.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a254631_R1
