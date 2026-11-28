import OMAStatements.S_oeis_a219454

-- Reduction oeis-a219454.R1 of oeis-a219454: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a219454_R1

open OMA.S_oeis_a219454
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (4 - 32 * X + 121 * X ^ 2 - 283 * X ^ 3 + 459 * X ^ 4 - 553 * X ^ 5 + 525 * X ^ 6 - 411 * X ^ 7 + 271 * X ^ 8 - 149 * X ^ 9 + 71 * X ^ 10 - 29 * X ^ 11 + 8 * X ^ 12 - X ^ 13)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 14 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219454.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a219454_R1
