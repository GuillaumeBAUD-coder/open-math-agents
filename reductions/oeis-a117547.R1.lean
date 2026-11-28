import OMAStatements.S_oeis_a117547

-- Reduction oeis-a117547.R1 of oeis-a117547: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a117547_R1

open OMA.S_oeis_a117547
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ))

/-- Step H2 of the reduction. -/
def H2 : Prop := ((1 - 6 * X + X ^ 2) * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X ^ 2 * (2 - X - 52 * X ^ 2 + 9 * X ^ 3))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a117547.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a117547_R1
