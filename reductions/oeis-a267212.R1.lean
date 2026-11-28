import OMAStatements.S_oeis_a267212

-- Reduction oeis-a267212.R1 of oeis-a267212: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a267212_R1

open OMA.S_oeis_a267212
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) = 1 + X + 5 * X ^ 2 + X ^ 3 + 5 * X ^ 4 + X ^ 5 + 3 * X ^ 6 - 3 * X ^ 7)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a267212.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a267212_R1
