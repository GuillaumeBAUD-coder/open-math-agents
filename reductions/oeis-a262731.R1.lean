import OMAStatements.S_oeis_a262731

-- Reduction oeis-a262731.R1 of oeis-a262731: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a262731_R1

open OMA.S_oeis_a262731

/-- Step H1 of the reduction. -/
def H1 : Prop := (S 2).Infinite

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 2 ≤ n → (S n).Infinite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a262731.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a262731_R1
