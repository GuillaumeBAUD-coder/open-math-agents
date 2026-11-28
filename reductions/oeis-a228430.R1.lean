import OMAStatements.S_oeis_a228430

-- Reduction oeis-a228430.R1 of oeis-a228430: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a228430_R1

open OMA.S_oeis_a228430

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 ≤ n → ((∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + y * (y + 1) / 2).Prime) ↔
        n ≠ 1 ∧ n ≠ 6))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 3, 14, 25} : Finset ℕ) →
        ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 3 + y * (y + 1) / 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228430.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a228430_R1
