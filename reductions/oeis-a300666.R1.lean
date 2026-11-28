import OMAStatements.S_oeis_a300666

-- Reduction oeis-a300666.R1 of oeis-a300666: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a300666_R1

open OMA.S_oeis_a300666

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ∃ x y z w : ℕ, z ≤ w ∧ (IsSquare x ∨ IsSquare (2 * y)) ∧ IsSquare (x + 3 * y) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, n ≠ 3 → ∃ x y z w : ℕ, (IsSquare x ∨ IsSquare (2 * y)) ∧
        (∃ s : ℤ, 3 * (x : ℤ) - y = s ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a300666.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a300666_R1
