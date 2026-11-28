import OMAStatements.S_oeis_a223616

-- Reduction oeis-a223616.R1 of oeis-a223616: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a223616_R1

open OMA.S_oeis_a223616
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 9 =
      11 + 22 * X ^ 1 + 183 * X ^ 2 + 14 * X ^ 3 + 158 * X ^ 4 - 56 * X ^ 5 + 35 * X ^ 6 - 8 * X ^ 7 + X ^ 8)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n > 9, (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a223616.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a223616_R1
