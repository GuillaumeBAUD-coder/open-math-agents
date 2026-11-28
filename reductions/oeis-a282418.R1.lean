import OMAStatements.S_oeis_a282418

-- Reduction oeis-a282418.R1 of oeis-a282418: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a282418_R1

open OMA.S_oeis_a282418
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 7 * a (n - 2) - 14 * a (n - 4) + 8 * a (n - 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) : PowerSeries ℚ) = 1 + X - X ^ 2 - 4 * X ^ 3)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a282418.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a282418_R1
