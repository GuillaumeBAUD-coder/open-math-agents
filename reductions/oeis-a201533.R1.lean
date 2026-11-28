import OMAStatements.S_oeis_a201533

-- Reduction oeis-a201533.R1 of oeis-a201533: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a201533_R1

open OMA.S_oeis_a201533
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (3 - 18 * X + 52 * X ^ 2 - 84 * X ^ 3 + 76 * X ^ 4 - 25 * X ^ 5 - 19 * X ^ 6 + 20 * X ^ 7 + X ^ 8 - 9 * X ^ 9 + 5 * X ^ 10 - X ^ 11)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 12 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a201533.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a201533_R1
