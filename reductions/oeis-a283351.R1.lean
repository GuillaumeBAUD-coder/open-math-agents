import OMAStatements.S_oeis_a283351

-- Reduction oeis-a283351.R1 of oeis-a283351: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283351_R1

open OMA.S_oeis_a283351
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) = 1 - 100 * X ^ 2 + 110 * X ^ 3)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-20 - 9 * (-10 : ℚ) ^ n + 11 * (10 : ℚ) ^ n) / 180)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a283351.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a283351_R1
