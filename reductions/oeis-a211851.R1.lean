import OMAStatements.S_oeis_a211851

-- Reduction oeis-a211851.R1 of oeis-a211851: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a211851_R1

open OMA.S_oeis_a211851
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (196 - 419 * X + 457 * X ^ 2 - 241 * X ^ 3 + 50 * X ^ 4)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a211851.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a211851_R1
