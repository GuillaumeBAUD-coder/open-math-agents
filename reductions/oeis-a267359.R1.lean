import OMAStatements.S_oeis_a267359

-- Reduction oeis-a267359.R1 of oeis-a267359: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a267359_R1

open OMA.S_oeis_a267359
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 10001 * a (n - 2) - 10000 * a (n - 4))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ) = 1 + 11 * X + 1099 * X ^ 2 - 8900 * X ^ 3 + 108900 * X ^ 4 - 10990000 * X ^ 5 + 890000 * X ^ 6 + 11000000 * X ^ 7 - 1000000 * X ^ 8)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a267359.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a267359_R1
