import OMAStatements.S_oeis_a183245

-- Reduction oeis-a183245.R1 of oeis-a183245: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a183245_R1

open OMA.S_oeis_a183245
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 3 * X) * (1 - 4 * X)) =
      X * (9 - 34 * X + 17 * X ^ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 12 * a (n - 2))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a183245.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a183245_R1
