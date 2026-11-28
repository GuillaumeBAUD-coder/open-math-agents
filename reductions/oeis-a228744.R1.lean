import OMAStatements.S_oeis_a228744

-- Reduction oeis-a228744.R1 of oeis-a228744: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228744_R1

open OMA.S_oeis_a228744
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (88 + 367 * X + 26 * X ^ 2 - 353 * X ^ 3 + 86 * X ^ 4 - 21 * X ^ 5 + 8 * X ^ 6 - X ^ 7)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228744.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228744_R1
