import OMAStatements.S_oeis_a270006

-- Reduction oeis-a270006.R1 of oeis-a270006: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a270006_R1

open OMA.S_oeis_a270006
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (1 - (-1 : ℚ) ^ n) * (2 * (n : ℚ) + 1) ^ 2 / 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = 0)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = (2 * (n : ℚ) + 1) ^ 2)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧ (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) = 1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7) )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a270006.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a270006_R1
