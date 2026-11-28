import OMAStatements.S_oeis_a074399

-- Reduction oeis-a074399.R1 of oeis-a074399: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a074399_R1

open OMA.S_oeis_a074399

/-- Step H1 of the reduction. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → Set.Infinite {n : ℕ | 2 ≤ n ∧ (largestPrimeFactor (n * (n + 1)) : ℝ) < (Real.log (n : ℝ)) ^ (2 + ε)}

/-- Step H2 of the reduction. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → Set.Finite {n : ℕ | 2 ≤ n ∧ (largestPrimeFactor (n * (n + 1)) : ℝ) < (Real.log (n : ℝ)) ^ (2 - ε)}

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a074399.main := by
  intro h1 h2 x1 x2
  exact ⟨h1 x1 x2, h2 x1 x2⟩

end OMA.R_oeis_a074399_R1
