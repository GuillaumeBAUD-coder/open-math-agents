import OMAStatements.S_oeis_a257663

-- Reduction oeis-a257663.R1 of oeis-a257663: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a257663_R1

open OMA.S_oeis_a257663

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare ((prime (k * n) : ℤ) - prime (k + n)))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsSquare (prime (k * n) + prime (k + n))

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a257663.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a257663_R1
