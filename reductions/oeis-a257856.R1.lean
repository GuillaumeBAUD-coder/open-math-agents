import OMAStatements.S_oeis_a257856

-- Reduction oeis-a257856.R1 of oeis-a257856: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a257856_R1

open OMA.S_oeis_a257856

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare (prime (k * n) - prime k))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ r : ℚ, 1 < r → ∃ m n : ℕ, 0 < n ∧ n < m ∧ r = (m : ℚ) / n ∧ IsSquare (prime m - prime n)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a257856.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a257856_R1
