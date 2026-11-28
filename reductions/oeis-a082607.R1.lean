import OMAStatements.S_oeis_a082607

-- Reduction oeis-a082607.R1 of oeis-a082607: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a082607_R1

open OMA.S_oeis_a082607

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ a : ℕ → ℕ, IsA082607 a → Function.Injective a

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a : ℕ → ℕ, IsA082607 a → Set.range a = {k : ℕ | InA008784 k}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a082607.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a082607_R1
