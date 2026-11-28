import OMAStatements.S_oeis_a288661

-- Reduction oeis-a288661.R1 of oeis-a288661: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a288661_R1

open OMA.S_oeis_a288661
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2) : PowerSeries ℚ) = 1 + 10 * X - 110 * X ^ 2 - 10 * X ^ 3 + 1010 * X ^ 4 - 1000 * X ^ 6)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a288661.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a288661_R1
