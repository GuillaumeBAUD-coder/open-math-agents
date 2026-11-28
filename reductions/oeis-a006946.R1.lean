import OMAStatements.S_oeis_a006946

-- Reduction oeis-a006946.R1 of oeis-a006946: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a006946_R1

open OMA.S_oeis_a006946

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (Odd n → 2 * indepNum n + binaryNecklaces n = 2 ^ n + 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (Even n → 4 * indepNum n + binaryNecklaces (n + 1) = 2 ^ (n + 1) + 4)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a006946.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a006946_R1
