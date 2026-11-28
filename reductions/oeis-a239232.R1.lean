import OMAStatements.S_oeis_a239232

-- Reduction oeis-a239232.R1 of oeis-a239232: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a239232_R1

open OMA.S_oeis_a239232

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 15 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (p (n + k) - 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 38 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (p (n + k)).Prime

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a239232.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a239232_R1
