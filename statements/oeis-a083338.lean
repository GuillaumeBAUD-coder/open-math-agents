import Mathlib

/-!
# A083338: Number of partitions of odd numbers into three primes and of even numbers into two primes.

Source: https://oeis.org/A083338
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) > 0 for all n iff Goldbach's conjectures hold.
-/

namespace OMA.S_oeis_a083338

theorem main :
    (∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) ∧
    (∀ n : ℕ, Odd n → 7 ≤ n → ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n) := by
  sorry

end OMA.S_oeis_a083338
