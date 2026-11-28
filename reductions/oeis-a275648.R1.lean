import OMAStatements.S_oeis_a275648

-- Reduction oeis-a275648.R1 of oeis-a275648: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a275648_R1

open OMA.S_oeis_a275648

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → 0 < a n

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → (a n = 1 →
      n ∈ ({1, 3, 6, 7, 11, 14, 15, 23, 38, 47, 71, 77, 143, 152, 191, 608} : Finset ℕ) ∨
      ∃ k : ℕ, n = 2 ^ (2 * k + 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a275648.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a275648_R1
