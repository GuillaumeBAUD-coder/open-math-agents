import OMAStatements.S_oeis_a234200

-- Reduction oeis-a234200.R1 of oeis-a234200: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a234200_R1

open OMA.S_oeis_a234200
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 4 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 3 < n → n ≠ 9 → n ≠ 29 →
        ∃ k, 0 < k ∧ k < n ∧ (k * sigma 1 (n - k) - 1).Prime ∧ (k * sigma 1 (n - k) + 1).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234200.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a234200_R1
