import OMAStatements.S_oeis_a269585

-- Reduction oeis-a269585.R1 of oeis-a269585: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a269585_R1

open OMA.S_oeis_a269585
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, count n = (n:ℚ)^5 + 5*n^4 + 7*n^3 + 12*n^2 + 6*n + 1)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
      20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1))

/-- Step H3 of the reduction. -/
def H3 : Prop := (1-X)^6 * mk terms = (X * (32 + 37*X + 70*X^2 - 20*X^3 + 2*X^4 - X^5) :
      PowerSeries ℚ)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a269585.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a269585_R1
