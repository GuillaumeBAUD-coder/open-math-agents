import OMAStatements.S_oeis_a231633

-- Reduction oeis-a231633.R1 of oeis-a231633: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a231633_R1

open OMA.S_oeis_a231633

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → ∃ x, 0 < x ∧ x < n ∧ (x ^ 2 * (n - x) + 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 2 ≤ n → ∃ x, 0 < x ∧ x < n ∧ ((x * (n - x)) ^ 2 + x * (n - x) + 1).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a231633.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a231633_R1
