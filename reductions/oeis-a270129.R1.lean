import OMAStatements.S_oeis_a270129

-- Reduction oeis-a270129.R1 of oeis-a270129: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a270129_R1

open OMA.S_oeis_a270129
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = -1 / 2 * (-1 + (-1 : ℚ) ^ n) * (1 + 2 * (n : ℚ)) ^ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 ≤ n → Even n → (a n : ℚ) = 0)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 4 ≤ n → Odd n → (a n : ℚ) = 4 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 1)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, 10 ≤ n → (a n : ℚ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧ (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) = 1 + 4 * X + 2 * X ^ 2 + 32 * X ^ 3 - 12 * X ^ 4 + X ^ 5 + 14 * X ^ 6 - 10 * X ^ 7 - 5 * X ^ 8 + 5 * X ^ 9) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a270129.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a270129_R1
