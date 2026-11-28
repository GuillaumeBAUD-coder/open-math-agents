import OMAStatements.S_oeis_a226988

-- Reduction oeis-a226988.R1 of oeis-a226988: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a226988_R1

open OMA.S_oeis_a226988

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (10 - 38 * PowerSeries.X + 64 * PowerSeries.X ^ 2 - 31 * PowerSeries.X ^ 3 - 67 * PowerSeries.X ^ 4 + 148 * PowerSeries.X ^ 5 - 137 * PowerSeries.X ^ 6 + 56 * PowerSeries.X ^ 7 + 12 * PowerSeries.X ^ 8 - 26 * PowerSeries.X ^ 9 + 12 * PowerSeries.X ^ 10 - 2 * PowerSeries.X ^ 11)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 12 < n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a226988.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a226988_R1
