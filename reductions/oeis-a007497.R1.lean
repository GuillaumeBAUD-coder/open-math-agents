import OMAStatements.S_oeis_a007497

-- Reduction oeis-a007497.R1 of oeis-a007497: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a007497_R1

open OMA.S_oeis_a007497

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 2 ≤ n →
        (1 / 2 : ℝ) * Real.log n < (a (n + 1) : ℝ) / (a n : ℝ) ∧
          (a (n + 1) : ℝ) / (a n : ℝ) < 2 * Real.log n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 34 < n → 9 ∣ a n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007497.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a007497_R1
