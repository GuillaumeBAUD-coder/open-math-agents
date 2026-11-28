import OMAStatements.S_oeis_a250610

-- Reduction oeis-a250610.R1 of oeis-a250610: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250610_R1

open OMA.S_oeis_a250610

/-- Step H1 of the reduction. -/
def H1 : Prop := a 1 = 1013

/-- Step H2 of the reduction. -/
def H2 : Prop := a 2 = 2336

/-- Step H3 of the reduction. -/
def H3 : Prop := a 3 = 4353

/-- Step H4 of the reduction. -/
def H4 : Prop := ( a 4 = 7320 ∧ (∀ n : ℕ, 1 ≤ n → (a (n + 4) : ℤ) = 5 * a (n + 3) - 9 * a (n + 2) + 7 * a (n + 1) - 2 * a n) ∧ (∀ n : ℕ, 1 ≤ n → 1 * (a n : ℤ) = 128 + 2 ^ (n + 7) + 410 * ((n : ℕ) : ℤ) + 219 * ((n : ℕ) : ℤ) ^ 2) )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a250610.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a250610_R1
