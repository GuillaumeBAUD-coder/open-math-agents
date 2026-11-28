import OMAStatements.S_oeis_a228222

-- Reduction oeis-a228222.R1 of oeis-a228222: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228222_R1

open OMA.S_oeis_a228222
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := ordinary * (1-X)^6 =
      X*(127+1297*X+3604*X^2+2168*X^3-475*X^4-X^5)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 6 < n → (a n : ℚ) =
      6*(a (n-1):ℚ) - 15*(a (n-2):ℚ) + 20*(a (n-3):ℚ)
      - 15*(a (n-4):ℚ) + 6*(a (n-5):ℚ) - (a (n-6):ℚ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228222.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228222_R1
