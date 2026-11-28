import OMAStatements.S_oeis_a282972

-- Reduction oeis-a282972.R1 of oeis-a282972: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a282972_R1

open OMA.S_oeis_a282972

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ∃ x y z w : ℕ, 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (79 * (y : ℤ) ^ 2 - 220 * y * z + 205 * (z : ℤ) ^ 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (169 * (y : ℤ) ^ 2 - 444 * y * z + 396 * (z : ℤ) ^ 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ 4 * x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (289 * (y : ℤ) ^ 2 - 654 * y * z + 401 * (z : ℤ) ^ 2)

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a282972.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a282972_R1
