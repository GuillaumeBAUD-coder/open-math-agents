import OMAStatements.S_oeis_a270985

-- Reduction oeis-a270985.R1 of oeis-a270985: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a270985_R1

open OMA.S_oeis_a270985
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (320 - 27 * (2 : ℚ) ^ (3 + n) + 175 * (4 : ℚ) ^ n + 384 * (n : ℚ)) / 144)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 8 * a (n - 1) - 21 * a (n - 2) + 22 * a (n - 3) - 8 * a (n - 4))

/-- Step H3 of the reduction. -/
def H3 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = (1 + X) * (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3 + 16 * X ^ 4 - 8 * X ^ 5))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a270985.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a270985_R1
