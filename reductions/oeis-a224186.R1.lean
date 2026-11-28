import OMAStatements.S_oeis_a224186

-- Reduction oeis-a224186.R1 of oeis-a224186: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a224186_R1

open OMA.S_oeis_a224186

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + 1 * (a (n - 9) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 : ℚ) + (2173/420 : ℚ) * (n : ℚ) + (56759/5040 : ℚ) * (n : ℚ) ^ 2 + (215/16 : ℚ) * (n : ℚ) ^ 3 + (615/64 : ℚ) * (n : ℚ) ^ 4 + (169/40 : ℚ) * (n : ℚ) ^ 5 + (179/160 : ℚ) * (n : ℚ) ^ 6 + (55/336 : ℚ) * (n : ℚ) ^ 7 + (41/4032 : ℚ) * (n : ℚ) ^ 8)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a224186.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a224186_R1
