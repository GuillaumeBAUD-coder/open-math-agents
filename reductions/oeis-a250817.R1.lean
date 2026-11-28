import OMAStatements.S_oeis_a250817

-- Reduction oeis-a250817.R1 of oeis-a250817: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250817_R1

open OMA.S_oeis_a250817

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (171 / 4) * (n : ℚ) ^ 4 + 390 * (n : ℚ) ^ 3 + (5627 / 4) * (n : ℚ) ^ 2 + (3575 / 2) * (n : ℚ) + 729)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a250817.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a250817_R1
