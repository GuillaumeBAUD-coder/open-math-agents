import OMAStatements.S_oeis_a235728

-- Reduction oeis-a235728.R1 of oeis-a235728: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a235728_R1

open OMA.S_oeis_a235728

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 191))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 8 < n → n ≠ 32 → ∃ k : ℕ, 0 < k ∧ k + 2 < n ∧
      Good (ArithmeticFunction.sigma 1 k + Nat.totient (n - k) / 2))

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a235728.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a235728_R1
