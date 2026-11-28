import OMAStatements.S_oeis_a279144

-- Reduction oeis-a279144.R1 of oeis-a279144: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a279144_R1

open OMA.S_oeis_a279144
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 16 ≤ n → (a n : ℚ) = -2 * a (n - 1) + 8 * a (n - 3) + 16 * a (n - 4) + a (n - 8) + 2 * a (n - 9) - 8 * a (n - 11) - 16 * a (n - 12))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 : PowerSeries ℚ) = -14336 * X ^ 15 - 2048 * X ^ 14 + 224 * X ^ 13 + 32 * X ^ 12 + 224 * X ^ 9 + 36 * X ^ 8 + 2 * X ^ 7 + 5 * X ^ 6 + 2 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a279144.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a279144_R1
