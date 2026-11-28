import OMAStatements.S_oeis_a250271

-- Reduction oeis-a250271.R1 of oeis-a250271: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250271_R1

open OMA.S_oeis_a250271
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      X * (3 - 16 * X + 21 * X ^ 2 + 24 * X ^ 3 - 60 * X ^ 4 + 24 * X ^ 5)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → (a n : ℤ) = 5 * 3 ^ (n - 1) - (2 ^ n - 2) * n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a250271.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a250271_R1
