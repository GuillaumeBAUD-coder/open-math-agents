import OMAStatements.S_oeis_a223734

-- Reduction oeis-a223734.R1 of oeis-a223734: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223734_R1

open OMA.S_oeis_a223734

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 4075

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | n ≤ 4075 ∧ IsTerm n}.ncard = 185

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, IsTerm n → n ≤ 4075

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a223734.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a223734_R1
