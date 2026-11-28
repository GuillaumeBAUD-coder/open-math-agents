import Mathlib

/-!
# A090688: First occurrence of primes in the progression k*x^2-1.

Source: https://oeis.org/A090688
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

If k>2 is a square, there is no entry corresponding to k*x^2-1. Bunyakovsky's conjecture
implies that there are primes for all other k.
-/

namespace OMA.S_oeis_a090688

theorem main :
    ∀ k : ℕ, 1 ≤ k → ¬ (2 < k ∧ IsSquare k) →
      ∃ x : ℕ, 1 ≤ x ∧ Nat.Prime (k * x ^ 2 - 1) := by
  sorry

end OMA.S_oeis_a090688
