import OMAStatements.S_oeis_a219465

-- Reduction oeis-a219465.R1 of oeis-a219465: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a219465_R1

open OMA.S_oeis_a219465
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (4 - 13 * X + 19 * X ^ 2 - 7 * X ^ 3 - 8 * X ^ 4 + 10 * X ^ 5 - 2 * X ^ 6 - X ^ 7)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219465.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a219465_R1
