import OMAStatements.S_oeis_a022566

-- Reduction oeis-a022566.R1 of oeis-a022566: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a022566_R1

open OMA.S_oeis_a022566

/-- Step H1 of the reduction. -/
def H1 : Prop := {n : ℕ | ¬ IsSum4Cubes n}.Finite

/-- Step H2 of the reduction. -/
def H2 : Prop := {n : ℕ | ¬ IsSum4Cubes n}.ncard = 113936676

/-- Step H3 of the reduction. -/
def H3 : Prop := ¬ IsSum4Cubes 7373170279850

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n > 7373170279850, IsSum4Cubes n

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a022566.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a022566_R1
