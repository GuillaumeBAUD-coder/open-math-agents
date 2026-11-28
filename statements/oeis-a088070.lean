import Mathlib

/-!
# A088070: Numbers sandwiched between two numbers with the same number of prime divisors

Source: https://oeis.org/A088070
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Numbers n >= 2 sandwiched between two numbers n - 1 and n + 1 having the same
number of distinct prime divisors: omega(n - 1) = omega(n + 1).
Conjecture: For every k there is a string of k successive integers in this sequence.
-/

namespace OMA.S_oeis_a088070

/-- `n` belongs to A088070 if `n ≥ 2` and `ω(n - 1) = ω(n + 1)`. -/
def InSeq (n : ℕ) : Prop :=
  2 ≤ n ∧ (n - 1).primeFactors.card = (n + 1).primeFactors.card

theorem main :
    ∀ k : ℕ, ∃ m : ℕ, ∀ i : ℕ, i < k → InSeq (m + i) := by
  sorry

end OMA.S_oeis_a088070
