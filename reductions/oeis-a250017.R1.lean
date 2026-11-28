import OMAStatements.S_oeis_a250017

-- Reduction oeis-a250017.R1 of oeis-a250017: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250017_R1

open OMA.S_oeis_a250017
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, total n = (n:ℚ)^8 + 41/35*(n:ℚ)^7 + 56/15*(n:ℚ)^6 + 22/5*(n:ℚ)^5 +
      19/3*(n:ℚ)^4 + 17/5*(n:ℚ)^3 - 16/15*(n:ℚ)^2 + 36/35*n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, total (n+9) = 9*total (n+8) - 36*total (n+7) + 84*total (n+6) - 126*total (n+5) +
      126*total (n+4) - 84*total (n+3) + 36*total (n+2) - 9*total (n+1) + total n)

/-- Step H3 of the reduction. -/
def H3 : Prop := (1-X)^9 * mk total =
      (4*X*(5+183*X+1506*X^2+3974*X^3+3441*X^4+903*X^5+68*X^6) : PowerSeries ℚ)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a250017.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a250017_R1
