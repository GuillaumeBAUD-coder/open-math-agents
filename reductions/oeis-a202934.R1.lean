import OMAStatements.S_oeis_a202934

-- Reduction oeis-a202934.R1 of oeis-a202934: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a202934_R1

open OMA.S_oeis_a202934
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (104976 - 580958 * X + 1353236 * X ^ 2 - 1692959 * X ^ 3 + 1197415 * X ^ 4 - 453495 * X ^ 5 + 71809 * X ^ 6)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a202934.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a202934_R1
