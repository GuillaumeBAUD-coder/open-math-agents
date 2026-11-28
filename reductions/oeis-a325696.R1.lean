import OMAStatements.S_oeis_a325696

-- Reduction oeis-a325696.R1 of oeis-a325696: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a325696_R1

open OMA.S_oeis_a325696
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ k : ℕ, term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1))

/-- Step H2 of the reduction. -/
def H2 : Prop := ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series = 6*X^7*(1+X+2*X^2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a325696.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a325696_R1
