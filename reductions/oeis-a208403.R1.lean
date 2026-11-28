import OMAStatements.S_oeis_a208403

-- Reduction oeis-a208403.R1 of oeis-a208403: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a208403_R1

open OMA.S_oeis_a208403
open PowerSeries Finset

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - 7 * X) * (1 - 63 * X)) =
      X * (5 - 168 * X + 147 * X ^ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → (a n : ℚ) = 2 / 27 * 7 ^ (n - 1) * (27 + 4 * 9 ^ n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a208403.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a208403_R1
