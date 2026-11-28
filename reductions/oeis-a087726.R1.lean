import OMAStatements.S_oeis_a087726

-- Reduction oeis-a087726.R1 of oeis-a087726: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a087726_R1

open OMA.S_oeis_a087726

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 0 < n → (a n = n ^ 2 ↔ Squarefree n))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ p k : ℕ, p.Prime → 0 < k →
      4 * (a (p ^ k) : ℤ) =
        (1 + 3 * (p : ℤ) ^ 2 + 2 * k * ((p : ℤ) ^ 2 - 1) +
          (-1 : ℤ) ^ k * ((p : ℤ) ^ 2 - 1)) * (p : ℤ) ^ (2 * k - 2))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a087726.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a087726_R1
