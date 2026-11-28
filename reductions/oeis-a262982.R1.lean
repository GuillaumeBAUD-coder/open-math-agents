import OMAStatements.S_oeis_a262982

-- Reduction oeis-a262982.R1 of oeis-a262982: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a262982_R1

open OMA.S_oeis_a262982

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → (a n = 1 → n ∈ ({2, 6, 20, 26, 40, 82, 89, 105, 305, 416, 470, 725, 6135,
      25430, 90285} : Finset ℕ))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a262982.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a262982_R1
