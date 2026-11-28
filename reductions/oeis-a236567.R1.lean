import OMAStatements.S_oeis_a236567

-- Reduction oeis-a236567.R1 of oeis-a236567: splits the target conjunction into 4 steps.
-- Credit: @kernl

namespace OMA.R_oeis_a236567_R1

open OMA.S_oeis_a236567

/-- Step H1 of the reduction. -/
def H1 : Prop := (∀ n : ℕ, 5 < n → 0 < a n)

/-- Step H2 of the reduction. -/
def H2 : Prop := (∀ n : ℕ, 31 < n → ∃ k, 0 < k ∧ k < n - 2 ∧
        IsSquare (Nat.totient k + Nat.totient (n - k) / 2))

/-- Step H3 of the reduction. -/
def H3 : Prop := (∀ n : ℕ, 70 < n → n ≠ 150 → ∃ k, 0 < k ∧ k < n ∧
        IsSquare (Nat.totient k + Nat.totient (n - k)))

/-- Step H4 of the reduction. -/
def H4 : Prop := ( (∀ n : ℕ, 5 < n → ∃ k, 0 < k ∧ k < n - 2 ∧
        ∃ t : ℕ, Nat.totient k + Nat.totient (n - k) / 2 = t * (t + 1) / 2) ∧ ∀ n : ℕ, 20 ≤ n → ∃ k, 0 < k ∧ k < n ∧ Even (Nat.totient k + Nat.totient (n - k)) ∧ ∃ t : ℕ, (Nat.totient k + Nat.totient (n - k)) / 2 = t * (t + 1) / 2 )

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a236567.main := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_oeis_a236567_R1
