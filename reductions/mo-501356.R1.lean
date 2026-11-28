import OMAStatements.S_mo_501356

-- Reduction mo-501356.R1 of mo-501356: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_mo_501356_R1

open OMA.S_mo_501356

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3286 < n → ∃ i j k m : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < m ∧
      2 * n = squareIndexPrime i + squareIndexPrime j + squareIndexPrime k + squareIndexPrime m)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3200 < n → ∃ i j k m : ℕ,
      0 < m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
      2 * n + 1 = squareIndexPrime i + squareIndexPrime j + squareIndexPrime k + 2 * squareIndexPrime m)

theorem main : H1 → H2 → type_of% @OMA.S_mo_501356.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_mo_501356_R1
