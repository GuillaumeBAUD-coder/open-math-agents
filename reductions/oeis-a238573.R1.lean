import OMAStatements.S_oeis_a238573

-- Reduction oeis-a238573.R1 of oeis-a238573: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238573_R1

open OMA.S_oeis_a238573

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 6 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔ n = 2 ∨ n = 3 ∨ n = 8 ∨ n = 11 ∨ n = 17)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ (k : ℝ) < 3 * Real.sqrt n + 6 ∧ (prime (k * n) + 2).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, 6 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (prime (k ^ 2 * n) + 2).Prime) ∧ ∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ (prime (k ^ 2 * (n - k)) + 2).Prime )

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a238573.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a238573_R1
