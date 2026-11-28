import OMAStatements.S_oeis_a069051

-- Reduction oeis-a069051.R1 of oeis-a069051: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a069051_R1

open OMA.S_oeis_a069051

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 1 < n → n - 1 ∣ 2 ^ n - 2 →
      Squarefree ((2 ^ n - 2) / (n - 1)))

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 < n →
      ((∀ b : ℤ, b ^ n ≡ b [ZMOD (((n - 1) * n : ℕ) : ℤ)]) ↔
        n = 2 ∨ n = 3 ∨ n = 7 ∨ n = 43)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a069051.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a069051_R1
