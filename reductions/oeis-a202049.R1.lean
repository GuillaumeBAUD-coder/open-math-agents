import OMAStatements.S_oeis_a202049

-- Reduction oeis-a202049.R1 of oeis-a202049: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a202049_R1

open OMA.S_oeis_a202049

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      14 * PowerSeries.X * (69 - 316 * PowerSeries.X + 699 * PowerSeries.X ^ 2 - 918 * PowerSeries.X ^ 3 + 755 * PowerSeries.X ^ 4 - 384 * PowerSeries.X ^ 5 + 111 * PowerSeries.X ^ 6 - 14 * PowerSeries.X ^ 7)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a202049.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a202049_R1
