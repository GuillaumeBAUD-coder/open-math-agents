import Mathlib

/-!
# A074726: Numbers k such that sigma(F(k)) > 2*F(k) where F(k) is the k-th Fibonacci number.

Source: https://oeis.org/A074726
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: sigma(F(n)) > 2*F(n) if and only if F(n) is a Zumkeller number except for n = 12. Verified for n <= 371.
-/

namespace OMA.S_oeis_a074726

/-- A positive integer `m` is a Zumkeller number if its positive divisors can be partitioned into
two disjoint sets of equal sum. -/
def IsZumkeller (m : ℕ) : Prop :=
  0 < m ∧ ∃ S : Finset ℕ, S ⊆ m.divisors ∧ 2 * ∑ d ∈ S, d = ∑ d ∈ m.divisors, d

/-- Conjecture: for all `n ≠ 12` with `n ≥ 1`, `sigma(F(n)) > 2 * F(n)` iff `F(n)` is a Zumkeller number. -/
theorem main :
    ∀ n : ℕ, 0 < n → n ≠ 12 →
      (2 * Nat.fib n < ArithmeticFunction.sigma 1 (Nat.fib n) ↔ IsZumkeller (Nat.fib n)) := by sorry

end OMA.S_oeis_a074726
