import OMAStatements.S_oeis_a253229

-- Reduction oeis-a253229.R1 of oeis-a253229: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a253229_R1

open OMA.S_oeis_a253229
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X)) =
        X * (2470 - 8192 * X + 4681 * X ^ 2 + 8417 * X ^ 3 - 11033 * X ^ 4 + 3599 * X ^ 5 - 9 * X ^ 6 + X ^ 7)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 4 < n → (a n : ℚ) = 1128 + 2451 * 2 ^ (n - 5) + 402 * n + 33 * n ^ 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a253229.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a253229_R1
