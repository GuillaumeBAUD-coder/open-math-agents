import OMAStatements.S_oeis_a282986

-- Reduction oeis-a282986.R1 of oeis-a282986: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a282986_R1

open OMA.S_oeis_a282986
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 34 ≤ n → (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) = -4096 * X ^ 33 - 6144 * X ^ 32 + 5872 * X ^ 31 + 2144 * X ^ 30 + 1296 * X ^ 29 + 720 * X ^ 28 - 79 * X ^ 27 + 394 * X ^ 26 + 159 * X ^ 25 - 165 * X ^ 24 - 202 * X ^ 23 + 47 * X ^ 22 + 59 * X ^ 21 - 50 * X ^ 20 + 55 * X ^ 19 - 30 * X ^ 18 + 16 * X ^ 17 + 15 * X ^ 16 - 10 * X ^ 15 - 11 * X ^ 14 + 6 * X ^ 13 - 8 * X ^ 12 + 13 * X ^ 11 + 2 * X ^ 10 - X ^ 9 + 10 * X ^ 8 - 8 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 + X ^ 4 + 9 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a282986.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a282986_R1
