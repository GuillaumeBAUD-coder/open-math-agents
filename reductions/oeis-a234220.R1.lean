import OMAStatements.S_oeis_a234220

-- Reduction oeis-a234220.R1 of oeis-a234220: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a234220_R1

open OMA.S_oeis_a234220

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * a (n - 1) + 20 * a (n - 2) - 80 * a (n - 3))

/-- Step H2 of the reduction. -/
def H2 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 4 ^ (2 + n) + (2 : ℝ) ^ ((-1 : ℤ) + n) *
      (5 : ℝ) ^ (((-1 : ℝ) + n) / 2) *
      (20 - 20 * (-1) ^ n + 9 * Real.sqrt 5 + 9 * (-1) ^ n * Real.sqrt 5))

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a234220.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a234220_R1
