import OMAStatements.S_oeis_a045917

-- Reduction oeis-a045917.R1 of oeis-a045917: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a045917_R1

open OMA.S_oeis_a045917

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 ≤ n → (∃ p, InDecomp n p) →
        ((∀ p, InDecomp n p → (2 * n + p).Prime) ↔ n = 4 ∨ n = 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ m : ℕ, ∃ n : ℕ, a n = m)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a045917.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a045917_R1
