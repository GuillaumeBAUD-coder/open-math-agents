import OMAStatements.S_oeis_a270488

-- Reduction oeis-a270488.R1 of oeis-a270488: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a270488_R1

open OMA.S_oeis_a270488

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, a n = 1 ↔
      n ∈ ({0, 1, 5, 7, 19, 35, 54, 62, 63, 197, 285, 339, 479, 505, 917} : Finset ℕ))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 2 < n →
      ∃ x y z : ℕ, 0 < x ∧ x ^ 2 + y * (y + 1) + z * (z ^ 2 + 1) = n)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a270488.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a270488_R1
