import OMAStatements.S_oeis_a237497

-- Reduction oeis-a237497.R1 of oeis-a237497: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a237497_R1

open OMA.S_oeis_a237497

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 10 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 51 < n → a n ≠ 1)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 10 < n → ∃ k, 0 < k ∧ k < n ∧ (2 * k + 1).Prime ∧
        (Nat.primeCounting (k * (n - k))).Prime

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a237497.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a237497_R1
