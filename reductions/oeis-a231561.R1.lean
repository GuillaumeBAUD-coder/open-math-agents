import OMAStatements.S_oeis_a231561

-- Reduction oeis-a231561.R1 of oeis-a231561: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a231561_R1

open OMA.S_oeis_a231561

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 < n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) ^ 2 + 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) - 1).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := ( ∀ n : ℕ, 3 ≤ n → ∃ x, 0 < x ∧ x < n ∧ (2 ^ x * (n - x) ^ 2 - 1).Prime )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a231561.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a231561_R1
