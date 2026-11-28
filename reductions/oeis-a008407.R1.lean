import OMAStatements.S_oeis_a008407

-- Reduction oeis-a008407.R1 of oeis-a008407: splits the target conjunction into 2 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a008407_R1

open OMA.S_oeis_a008407

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 3 ≤ n → (a (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)) < (a n : ℝ) ^ ((1 : ℝ) / n))

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 4 < n → 0 < (a n : ℝ) / n - H n ∧
      (a n : ℝ) / n - H n < (Real.eulerMascheroniConstant + 2) / Real.log n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a008407.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a008407_R1
