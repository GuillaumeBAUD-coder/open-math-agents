import Mathlib

/-!
# OEIS A037020: Numbers whose sum of proper divisors is a prime

Source: https://oeis.org/A037020
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture (implied by Goldbach's conjecture): Every prime other than 2 and 5
is the sum of the proper divisors of some positive integer `n`.
-/

namespace OMA.S_oeis_a037020

theorem main :
    ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≠ 5 →
      ∃ n : ℕ, 0 < n ∧ ∑ d ∈ n.properDivisors, d = p := by
  sorry

end OMA.S_oeis_a037020
