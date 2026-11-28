import OMAStatements.S_oeis_a238278

-- Reduction oeis-a238278.R1 of oeis-a238278: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a238278_R1

open OMA.S_oeis_a238278

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 3 < n → ∃ p, p.Prime ∧ p < n ∧
        (Nat.primeCounting (p * n - 1) - Nat.primeCounting ((p - 1) * n)).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a238278.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a238278_R1
