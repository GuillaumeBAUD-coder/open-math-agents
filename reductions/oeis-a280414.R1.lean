import OMAStatements.S_oeis_a280414

-- Reduction oeis-a280414.R1 of oeis-a280414: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a280414_R1

open OMA.S_oeis_a280414
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 32 ≤ n → (a n : ℚ) = a (n - 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 2 - 1 : PowerSeries ℚ) = 110000000000000000000000000000 * X ^ 31 + 10000000000000000000000000000 * X ^ 30 - 109000000000000000000000000000 * X ^ 29 - 9900000000000000000000000000 * X ^ 28 - 990000000000000000000000000 * X ^ 27 - 99000000000000000000000000 * X ^ 26 - 9900000000000000000000000 * X ^ 25 - 990000000000000000000000 * X ^ 24 - 99000000000000000000000 * X ^ 23 - 9900000000000000000000 * X ^ 22 - 990000000000000000000 * X ^ 21 - 99000000000000000000 * X ^ 20 - 9900000000000000000 * X ^ 19 - 990000000000000000 * X ^ 18 - 99000000000000000 * X ^ 17 - 9900000000000000 * X ^ 16 - 990000000000000 * X ^ 15 - 99000000000000 * X ^ 14 - 9900000000000 * X ^ 13 - 990000000000 * X ^ 12 - 99889000000 * X ^ 11 - 9999000000 * X ^ 10 - 100000000 * X ^ 9 - 10900000 * X ^ 7 - 990000 * X ^ 6 - 100000 * X ^ 5 - 10000 * X ^ 4 - 100 * X ^ 3 - 11 * X - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a280414.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a280414_R1
