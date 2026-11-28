import OMAStatements.S_oeis_a233918

-- Reduction oeis-a233918.R1 of oeis-a233918: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a233918_R1

open OMA.S_oeis_a233918
open ArithmeticFunction

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 5 < n → n ≠ 19 → ∃ k, 0 < k ∧ k < n ∧
        (Nat.totient k + Nat.totient (n - k) - 1).Prime ∧
        (Nat.totient k + Nat.totient (n - k) + 1).Prime)

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n ∧ Even (Nat.totient k) ∧ Even (Nat.totient (n - k)) ∧
        ((Nat.totient k / 2) ^ 2 + (Nat.totient (n - k) / 2) ^ 2).Prime)

/-- Step H4 of the reduction. -/
def H4 : Prop := ∀ n : ℕ, 8 < n → ∃ k, 0 < k ∧ k < n ∧ Even (sigma 1 k + Nat.totient (n - k)) ∧
        ((sigma 1 k + Nat.totient (n - k)) / 2).Prime

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a233918.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a233918_R1
