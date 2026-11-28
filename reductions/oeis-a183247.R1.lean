import OMAStatements.S_oeis_a183247

-- Reduction oeis-a183247.R1 of oeis-a183247: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a183247_R1

open OMA.S_oeis_a183247
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 5 * X) * (1 - 8 * X) * (1 - 9 * X)) =
      X * (265 - 4122 * X + 17394 * X ^ 2 - 7150 * X ^ 3 - 29191 * X ^ 4 - 100844 * X ^ 5)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 22 * a (n - 1) - 157 * a (n - 2) + 360 * a (n - 3))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a183247.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a183247_R1
