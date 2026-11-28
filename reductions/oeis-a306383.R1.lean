import OMAStatements.S_oeis_a306383

-- Reduction oeis-a306383.R1 of oeis-a306383: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a306383_R1

open OMA.S_oeis_a306383

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 138158 < n → ∃ x y z : ℕ, x * (2 * x + 1) + y * (2 * y + 1) + z * (2 * z + 1) = n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 146858 < n → ∃ x y z : ℕ, x * (2 * x - 1) + y * (2 * y - 1) + z * (2 * z - 1) = n)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 33066 < n → ∃ x y z : ℕ,
        x * (3 * x - 1) / 2 + y * (3 * y - 1) / 2 + z * (3 * z - 1) / 2 = n

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a306383.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a306383_R1
