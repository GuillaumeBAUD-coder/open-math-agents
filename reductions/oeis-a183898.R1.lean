import OMAStatements.S_oeis_a183898

-- Reduction oeis-a183898.R1 of oeis-a183898: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a183898_R1

open OMA.S_oeis_a183898
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 ≤ n → 6 * a n = (n : ℤ)^3 + 15*(n : ℤ)^2 + 50*(n : ℤ) - 84)

/-- Step H2 of the reduction. -/
def H2 : Prop := (PowerSeries.mk a * (1 - X)^4 = X*(5 - 6*X + 12*X^2 - 18*X^3 + 8*X^4))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 5 < n → a n = 4*a (n-1) - 6*a (n-2) + 4*a (n-3) - a (n-4))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a183898.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a183898_R1
