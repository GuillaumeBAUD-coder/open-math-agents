import OMAStatements.S_oeis_a283402

-- Reduction oeis-a283402.R1 of oeis-a283402: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283402_R1

open OMA.S_oeis_a283402
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 27 ≤ n → (a n : ℚ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (2 * X - 1) * (2 * X + 1) : PowerSeries ℚ) = -12 * X ^ 26 + 8 * X ^ 25 + 3 * X ^ 24 - 2 * X ^ 23 - 52 * X ^ 12 + 40 * X ^ 11 + 17 * X ^ 10 - 2 * X ^ 9 - X ^ 8 - 2 * X ^ 7 + 4 * X ^ 6 + X ^ 4 + 2 * X ^ 3 - X ^ 2 - X + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a283402.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a283402_R1
