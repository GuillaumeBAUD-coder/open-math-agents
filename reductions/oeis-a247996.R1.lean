import OMAStatements.S_oeis_a247996

-- Reduction oeis-a247996.R1 of oeis-a247996: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a247996_R1

open OMA.S_oeis_a247996
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X)) =
      4 * X * (8 + 51 * X + 91 * X ^ 2 + 106 * X ^ 3 + 21 * X ^ 4 + 83 * X ^ 5)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n) / 2)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, Odd n →
      (a n : ℚ) = (2 * n ^ 6 + n ^ 5 + 35 * n ^ 4 - 5 * n ^ 3 + 10 * n ^ 2 + 36 * n - 15) / 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a247996.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a247996_R1
