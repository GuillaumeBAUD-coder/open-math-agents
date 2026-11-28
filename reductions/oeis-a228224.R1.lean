import OMAStatements.S_oeis_a228224

-- Reduction oeis-a228224.R1 of oeis-a228224: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228224_R1

open OMA.S_oeis_a228224
open PowerSeries

/-- Step H1 of the reduction. -/
def H1 : Prop := ordinary * (1-X)^8 = X*(511 + 15083*X + 103401*X^2 + 256585*X^3 + 252785*X^4 + 16749*X^5 - 40313*X^6 - X^7)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 8 < n → (a n : ℚ) = 8*(a (n-1):ℚ) - 28*(a (n-2):ℚ) + 56*(a (n-3):ℚ) - 70*(a (n-4):ℚ) + 56*(a (n-5):ℚ) - 28*(a (n-6):ℚ) + 8*(a (n-7):ℚ) - (a (n-8):ℚ))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228224.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228224_R1
