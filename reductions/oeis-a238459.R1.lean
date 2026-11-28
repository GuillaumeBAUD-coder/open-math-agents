import OMAStatements.S_oeis_a238459

-- Reduction oeis-a238459.R1 of oeis-a238459: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238459_R1

open OMA.S_oeis_a238459

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (q (n - p) + 1).Prime)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ p < n ∧ (q (n - p) - 1).Prime)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a238459.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a238459_R1
