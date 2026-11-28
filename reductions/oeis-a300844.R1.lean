import OMAStatements.S_oeis_a300844

-- Reduction oeis-a300844.R1 of oeis-a300844: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a300844_R1

open OMA.S_oeis_a300844

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (IsSquare x ∨ IsSquare (2 * y) ∨ IsSquare z) ∧
        IsSquare ((12 * x) ^ 2 + (21 * y) ^ 2 + (28 * z) ^ 2))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (IsSquare x ∨ IsSquare y ∨ IsSquare z) ∧ IsSquare (144 * x ^ 2 + 505 * y ^ 2 + 720 * z ^ 2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a300844.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a300844_R1
