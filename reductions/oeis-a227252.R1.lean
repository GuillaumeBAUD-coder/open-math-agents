import OMAStatements.S_oeis_a227252

-- Reduction oeis-a227252.R1 of oeis-a227252: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a227252_R1

open OMA.S_oeis_a227252

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      PowerSeries.X * (2 - 9 * PowerSeries.X + 21 * PowerSeries.X ^ 2 - 26 * PowerSeries.X ^ 3 + 20 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 7 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a227252.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a227252_R1
