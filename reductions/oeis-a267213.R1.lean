import OMAStatements.S_oeis_a267213

-- Reduction oeis-a267213.R1 of oeis-a267213: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a267213_R1

open OMA.S_oeis_a267213
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = a (n - 3) + a (n - 4) - a (n - 7))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) = X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a267213.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a267213_R1
