import Mathlib

/-!
# A072612: Minimal value of { |n - sigma(k)| : k > 0 }

Source: https://oeis.org/A072612
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = minimal value of { |n - sigma(k)| : k > 0 }.
Conjecture: S(n) = sum_{k=1..n} a(k) satisfies for n large enough:
n - (5/2)*sqrt(n) < S(n) < n - (3/2)*sqrt(n).
-/

namespace OMA.S_oeis_a072612

/-- Sum of positive divisors of `k`. -/
def sigma (k : ℕ) : ℕ :=
  ∑ d ∈ k.divisors, d

/-- `a n = min { |n - sigma(k)| : k > 0 }`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ k : ℕ, 1 ≤ k ∧ m = Int.natAbs ((n : ℤ) - (sigma k : ℤ)) }

/-- Partial sum `S(n) = ∑_{k=1..n} a(k)`. -/
noncomputable def S (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, a k

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) - (5 / 2 : ℝ) * Real.sqrt (n : ℝ) < (S n : ℝ) ∧
      (S n : ℝ) < (n : ℝ) - (3 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
  sorry

end OMA.S_oeis_a072612
