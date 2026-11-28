import OMAStatements.S_oeis_a262242

-- Reduction oeis-a262242.R1 of oeis-a262242: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a262242_R1

open OMA.S_oeis_a262242

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 ≤ n → a n = 2 ^ (n - 5) * (2 ^ n + 4))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 8 * a (n - 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((2 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
      PowerSeries.X * (240 * PowerSeries.X ^ 6 + 28 * PowerSeries.X ^ 5 - 70 * PowerSeries.X ^ 4 +
        24 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 - 12 * PowerSeries.X + 3)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a262242.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a262242_R1
