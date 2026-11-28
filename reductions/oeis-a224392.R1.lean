import OMAStatements.S_oeis_a224392

-- Reduction oeis-a224392.R1 of oeis-a224392: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a224392_R1

open OMA.S_oeis_a224392

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (353 / 181440) * (n : ℚ) ^ 9 + (17 / 560) * (n : ℚ) ^ 8 + (9731 / 30240) * (n : ℚ) ^ 7 + (1283 / 720) * (n : ℚ) ^ 6 + (52457 / 8640) * (n : ℚ) ^ 5 + (776 / 45) * (n : ℚ) ^ 4 + (294499 / 11340) * (n : ℚ) ^ 3 + (28837 / 2520) * (n : ℚ) ^ 2 + (8207 / 126) * (n : ℚ) - 18)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a224392.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a224392_R1
