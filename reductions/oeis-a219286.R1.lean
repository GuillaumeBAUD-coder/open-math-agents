import OMAStatements.S_oeis_a219286

-- Reduction oeis-a219286.R1 of oeis-a219286: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a219286_R1

open OMA.S_oeis_a219286
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (3 - 9 * X + 19 * X ^ 2 - 23 * X ^ 3 + 14 * X ^ 4 - 2 * X ^ 5 - X ^ 6)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219286.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a219286_R1
