import OMAStatements.S_opg_roller_coaster_permutations

-- Reduction opg-roller-coaster-permutations.R1 of opg-roller-coaster-permutations: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_opg_roller_coaster_permutations_R1

open OMA.S_opg_roller_coaster_permutations

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 3 ≤ n → (Even n → (RC n).card = 4)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 3 ≤ n → (∀ k : ℕ, n = 2 * k + 1 → ∃ j : ℕ, j ≤ k + 1 ∧ (RC n).card = 2 ^ j)

theorem main : H1 → H2 → type_of% @OMA.S_opg_roller_coaster_permutations.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_opg_roller_coaster_permutations_R1
