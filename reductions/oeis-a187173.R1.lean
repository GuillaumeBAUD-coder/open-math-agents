import OMAStatements.S_oeis_a187173

-- Reduction oeis-a187173.R1 of oeis-a187173: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a187173_R1

open OMA.S_oeis_a187173
open PowerSeries in

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      4 * X ^ 4 * (4 - X) * (1 + X)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 3 < n → (a n : ℤ) = 12 * (n : ℤ) ^ 2 - 64 * (n : ℤ) + 80

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a187173.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a187173_R1
