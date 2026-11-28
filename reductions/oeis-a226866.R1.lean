import OMAStatements.S_oeis_a226866

-- Reduction oeis-a226866.R1 of oeis-a226866: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a226866_R1

open OMA.S_oeis_a226866

/-- Step H1 of the reduction. -/
def H1 : Prop := (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      PowerSeries.X * (4 - 11 * PowerSeries.X + 19 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a226866.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a226866_R1
