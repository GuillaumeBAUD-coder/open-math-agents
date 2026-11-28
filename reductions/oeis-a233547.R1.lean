import OMAStatements.S_oeis_a233547

-- Reduction oeis-a233547.R1 of oeis-a233547: splits the target conjunction into 3 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a233547_R1

open OMA.S_oeis_a233547
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 3 < n → ∃ k, 0 < k ∧ k < n ∧ (sigma 1 k * Nat.totient (n - k) - 1).Prime ∧
        (sigma 1 k * Nat.totient (n - k) + 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := ∀ n : ℕ, 5 < n → n ≠ 35 → ∃ k, 0 < k ∧ k < n ∧
        (Nat.totient k * Nat.totient (n - k) - 1).Prime ∧
        (2 * (Nat.totient k * Nat.totient (n - k) - 1) + 1).Prime

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a233547.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a233547_R1
