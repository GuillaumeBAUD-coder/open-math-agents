import Mathlib

/-!
# OEIS A030057: Least number not a sum of distinct divisors of n (Coleman's conjecture)

Source: https://oeis.org/A030057
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture (Jaycob Coleman, at A002093 / A030057): Every highly abundant number
other than 3 and 10 is a practical number (every positive integer `≤ n` is a sum
of distinct positive divisors of `n`).
-/

namespace OMA.S_oeis_a030057

def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

def IsHighlyAbundant (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → sigma m < sigma n

def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ∃ s ∈ n.divisors.powerset, ∑ d ∈ s, d = k

theorem main :
    ∀ n : ℕ, IsHighlyAbundant n → n ≠ 3 → n ≠ 10 → IsPractical n := by
  sorry

end OMA.S_oeis_a030057
