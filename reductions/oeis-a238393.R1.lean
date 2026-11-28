import OMAStatements.S_oeis_a238393

-- Reduction oeis-a238393.R1 of oeis-a238393: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238393_R1

open OMA.S_oeis_a238393

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → (a n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 13))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ (2 * p k * p n - 1).Prime

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a238393.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a238393_R1
