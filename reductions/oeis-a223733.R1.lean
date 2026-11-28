import OMAStatements.S_oeis_a223733

-- Reduction oeis-a223733.R1 of oeis-a223733: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223733_R1

open OMA.S_oeis_a223733

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 1885

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | n ≤ 1885 ∧ IsTerm n}.ncard = 147

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, IsTerm n → n ≤ 1885

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a223733.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a223733_R1
