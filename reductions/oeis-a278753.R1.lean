import OMAStatements.S_oeis_a278753

-- Reduction oeis-a278753.R1 of oeis-a278753: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a278753_R1

open OMA.S_oeis_a278753
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 111 * a (n - 2) - 1110 * a (n - 4) + 1000 * a (n - 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * (1000 * X ^ 6 - 1110 * X ^ 4 + 111 * X ^ 2 - 1 : PowerSeries ℚ) = 1000 * X ^ 5 - 1000 * X ^ 3 + 100 * X ^ 2 - 1)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a278753.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a278753_R1
