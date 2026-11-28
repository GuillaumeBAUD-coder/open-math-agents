import OMAStatements.S_oeis_a223681

-- Reduction oeis-a223681.R1 of oeis-a223681: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223681_R1

open OMA.S_oeis_a223681
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (8 + 8 * X + 36 * X ^ 2 - 30 * X ^ 3 + 27 * X ^ 4 - 4 * X ^ 5 + X ^ 6)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a223681.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a223681_R1
