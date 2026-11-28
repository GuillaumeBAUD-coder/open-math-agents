import OMAStatements.S_oeis_a065026

-- Reduction oeis-a065026.R1 of oeis-a065026: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a065026_R1

open OMA.S_oeis_a065026
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 17 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) + 4 * (a (n - 4) : ℤ) - 2 * (a (n - 6) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := ((1 - 2 * X ^ 2 - 4 * X ^ 4 + 2 * X ^ 6) *
        PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X * (1 - X) * (1 + 3 * X + 5 * X ^ 2 + 10 * X ^ 3 + 15 * X ^ 4 + 14 * X ^ 5 + 25 * X ^ 6
        + 10 * X ^ 7 + 8 * X ^ 8 + 18 * X ^ 9 + 42 * X ^ 10 - 402 * X ^ 12 - 552 * X ^ 13
        - 720 * X ^ 14 - 804 * X ^ 15))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a065026.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a065026_R1
