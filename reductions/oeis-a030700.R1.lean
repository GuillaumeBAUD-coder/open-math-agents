import OMAStatements.S_oeis_a030700

-- Reduction oeis-a030700.R1 of oeis-a030700: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a030700_R1

open OMA.S_oeis_a030700

/-- Step H1 of the reduction. -/
def H1 : Prop := IsTerm 68

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, IsTerm n → n ≤ 68

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a030700.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a030700_R1
