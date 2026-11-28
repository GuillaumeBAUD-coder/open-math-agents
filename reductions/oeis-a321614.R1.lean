import OMAStatements.S_oeis_a321614

-- Reduction oeis-a321614.R1 of oeis-a321614: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a321614_R1

open OMA.S_oeis_a321614

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X) ^ 2 *
          (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) *
          (1 - PowerSeries.X - PowerSeries.X ^ 2) *
          (1 - 3 * PowerSeries.X ^ 2)) =
      (1 - 2 * PowerSeries.X) *
        (1 - 6 * PowerSeries.X + 17 * PowerSeries.X ^ 2 - 18 * PowerSeries.X ^ 3 -
          2 * PowerSeries.X ^ 4 + 7 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 -
          3 * PowerSeries.X ^ 7))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 12 * a (n - 1) - 54 * a (n - 2) + 98 * a (n - 3) + 17 * a (n - 4) -
        346 * a (n - 5) + 505 * a (n - 6) - 210 * a (n - 7) - 120 * a (n - 8) +
        126 * a (n - 9) - 27 * a (n - 10))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a321614.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a321614_R1
