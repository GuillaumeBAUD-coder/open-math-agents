import OMAStatements.S_oeis_a274605

-- Reduction oeis-a274605.R1 of oeis-a274605: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a274605_R1

open OMA.S_oeis_a274605

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 23268

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ k : ℕ, 23268 < k → ¬ IsTerm k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a274605.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a274605_R1
