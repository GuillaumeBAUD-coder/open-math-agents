import OMAStatements.S_oeis_a300448

-- Reduction oeis-a300448.R1 of oeis-a300448: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a300448_R1

open OMA.S_oeis_a300448

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 2, 5} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 5, 17} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 5, 65} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a300448.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a300448_R1
