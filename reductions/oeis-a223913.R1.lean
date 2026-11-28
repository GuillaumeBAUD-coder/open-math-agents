import OMAStatements.S_oeis_a223913

-- Reduction oeis-a223913.R1 of oeis-a223913: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223913_R1

open OMA.S_oeis_a223913

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (23 / 40) * (n : ℚ) ^ 5 + (205 / 72) * (n : ℚ) ^ 4 + (143 / 24) * (n : ℚ) ^ 3 + (364 / 45) * (n : ℚ) ^ 2 + (82 / 15) * (n : ℚ) - 1)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a223913.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a223913_R1
