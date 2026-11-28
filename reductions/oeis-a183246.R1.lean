import OMAStatements.S_oeis_a183246

-- Reduction oeis-a183246.R1 of oeis-a183246: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a183246_R1

open OMA.S_oeis_a183246
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 4 * X) * (1 - 6 * X)) =
      2 * X * (22 - 117 * X + 82 * X ^ 2 + 124 * X ^ 3)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) - 24 * a (n - 2))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a183246.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a183246_R1
