import OMAStatements.S_oeis_a086818

-- Reduction oeis-a086818.R1 of oeis-a086818: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a086818_R1

open OMA.S_oeis_a086818

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, (Nat.digits 10 (a n)).count 1 = 3

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, ∀ d ∈ Nat.digits 10 (a n), d = 0 ∨ d = 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a086818.main := by
  intro h1 h2 x1
  exact ⟨h1 x1, h2 x1⟩

end OMA.R_oeis_a086818_R1
