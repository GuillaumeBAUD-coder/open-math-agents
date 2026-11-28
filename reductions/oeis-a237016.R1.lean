import OMAStatements.S_oeis_a237016

-- Reduction oeis-a237016.R1 of oeis-a237016: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a237016_R1

open OMA.S_oeis_a237016
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 1 ∨ n = 7 ∨ n = 17))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ IsSquare (Nat.totient k * sigma 1 (n - k) + 1))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 309 < n → ∃ k, 0 < k ∧ 2 * k < n ∧ IsSquare (sigma 1 k * sigma 1 (n - k))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a237016.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a237016_R1
