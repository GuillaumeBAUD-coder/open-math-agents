import OMAStatements.S_oeis_a183885

-- Reduction oeis-a183885.R1 of oeis-a183885: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a183885_R1

open OMA.S_oeis_a183885
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 ≤ n → a n = 3^(n+3) - 2*((n : ℤ)+4)^2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk a * ((1 - X)^3 * (1 - 3*X)) =
      X * (1 + 115*X - 83*X^2 - 285*X^3 + 410*X^4 - 150*X^5))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 6 < n → a n = 6*a (n-1) - 12*a (n-2) + 10*a (n-3) - 3*a (n-4))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a183885.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a183885_R1
