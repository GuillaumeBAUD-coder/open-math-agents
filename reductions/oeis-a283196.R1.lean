import OMAStatements.S_oeis_a283196

-- Reduction oeis-a283196.R1 of oeis-a283196: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a283196_R1

open OMA.S_oeis_a283196

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ x y z w : ℤ, 0 < w ∧ |y| ≤ |z| ∧ IsSquare (2 * x + y) ∧ IsSquare (2 * x + z) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → ∃ x y z w : ℤ, 0 ≤ x ∧ 0 < w ∧ IsSquare (x + y) ∧ IsSquare (x + 2 * z) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a283196.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a283196_R1
