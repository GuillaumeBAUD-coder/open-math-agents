import OMAStatements.S_oeis_a228220

-- Reduction oeis-a228220.R1 of oeis-a228220: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228220_R1

open OMA.S_oeis_a228220
open PowerSeries in

/-- Step H1 of the reduction. -/
def H1 : Prop := ordinary * (1-X)^4 = X*(31 + 75*X + 15*X^2 - X^3)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → (a n : ℚ) = 4*(a (n-1):ℚ) - 6*(a (n-2):ℚ) + 4*(a (n-3):ℚ) - (a (n-4):ℚ))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228220.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228220_R1
