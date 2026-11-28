import OMAStatements.S_oeis_a283170

-- Reduction oeis-a283170.R1 of oeis-a283170: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283170_R1

open OMA.S_oeis_a283170

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ∃ x y z w : ℤ, 0 ≤ x ∧ 0 ≤ w ∧ IsSquare (x + 2 * y) ∧ IsSquare (z + 2 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, ∃ x y z w : ℤ, 0 ≤ w ∧ IsSquare (x + 3 * y) ∧ IsSquare (z + 3 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, ∃ x y z w : ℤ, IsSquare (x + 2 * y) ∧ IsSquare (z + 3 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a283170.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a283170_R1
