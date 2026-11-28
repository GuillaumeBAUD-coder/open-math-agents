import OMAStatements.S_oeis_a272417

-- Reduction oeis-a272417.R1 of oeis-a272417: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a272417_R1

open OMA.S_oeis_a272417
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, (a n : ℚ) = 4 / 3 - (2 : ℚ) ^ (2 + n) + 11 * (4 : ℚ) ^ n / 3)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3))

/-- Step H3 of the reduction. -/
def H3 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = 1 + X + 2 * X ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a272417.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a272417_R1
