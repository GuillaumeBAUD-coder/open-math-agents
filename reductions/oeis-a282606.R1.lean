import OMAStatements.S_oeis_a282606

-- Reduction oeis-a282606.R1 of oeis-a282606: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a282606_R1

open OMA.S_oeis_a282606
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 14 ≤ n → (a n : ℚ) = a (n - 2) + 10000 * a (n - 4) - 10000 * a (n - 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 6 - 10000 * X ^ 4 - X ^ 2 + 1 : PowerSeries ℚ) = 10000 * X ^ 13 - 10010 * X ^ 9 + 990 * X ^ 8 - 100 * X ^ 7 - 1000 * X ^ 6 + 11010 * X ^ 5 + 900 * X ^ 4 + 100 * X ^ 3 + 110 * X ^ 2 + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a282606.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a282606_R1
