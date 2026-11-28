import OMAStatements.S_oeis_a225894

-- Reduction oeis-a225894.R1 of oeis-a225894: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a225894_R1

open OMA.S_oeis_a225894

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
      PowerSeries.X * (4 - 8 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a225894.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a225894_R1
