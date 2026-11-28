import OMAStatements.S_oeis_a228221

-- Reduction oeis-a228221.R1 of oeis-a228221: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228221_R1

open OMA.S_oeis_a228221
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := ordinary * (1-X)^5 = X*(63 + 350*X + 456*X^2 - 30*X^3 + X^4)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 5 < n → (a n : ℚ) = 5*(a (n-1):ℚ) - 10*(a (n-2):ℚ) + 10*(a (n-3):ℚ) - 5*(a (n-4):ℚ) + (a (n-5):ℚ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228221.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228221_R1
