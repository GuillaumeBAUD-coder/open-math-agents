import OMAStatements.S_oeis_a271017

-- Reduction oeis-a271017.R1 of oeis-a271017: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a271017_R1

open OMA.S_oeis_a271017
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 3 * (4 : ℚ) ^ n - 7)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) = 1 + 20 * X ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a271017.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a271017_R1
