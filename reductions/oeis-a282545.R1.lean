import OMAStatements.S_oeis_a282545

-- Reduction oeis-a282545.R1 of oeis-a282545: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a282545_R1

open OMA.S_oeis_a282545

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < y ∧ x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        IsSquare (y ^ 2 + 64 * z ^ 2 + 1024 * y * z))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ a b c : ℕ, (a, b, c) ∈ ({(1, 484, 44), (1, 666, 9), (16, 1336, 169), (25, 900, 36)} :
          Finset (ℕ × ℕ × ℕ)) →
        ∀ n : ℕ, ∃ x y z w : ℕ, x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
          IsSquare (a * y ^ 2 + b * y * z + c * z ^ 2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a282545.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a282545_R1
