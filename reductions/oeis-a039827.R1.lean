import OMAStatements.S_oeis_a039827

-- Reduction oeis-a039827.R1 of oeis-a039827: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a039827_R1

open OMA.S_oeis_a039827
open Polynomial

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 9 ≤ n → a n = n * (n + 1) / 2 - 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3))

/-- Step H3 of the reduction. -/
def H3 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 -
        2 * PowerSeries.X ^ 7 + 4 * PowerSeries.X ^ 6 - PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 3 + PowerSeries.X - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a039827.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a039827_R1
