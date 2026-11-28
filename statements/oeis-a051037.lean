import Mathlib

/-!
# A051037: O(log log n) error term for counting 5-smooth numbers

Source: https://oeis.org/A051037
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A051037: 5-smooth numbers, i.e., numbers whose prime divisors are all <= 5.

Statement:
Let s(n) = Card(k | a(k) < n) and f(n) = log(n*sqrt(30))^3 / (6*log(2)*log(3)*log(5)).
Conjecture: s(n) = f(n) + O(log log n).
-/

namespace OMA.S_oeis_a051037

/-- Number of 5-smooth positive integers strictly less than `n`. -/
def s (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun m => 0 < m ∧ ∀ p ∈ m.primeFactors, p ≤ 5)).card

/-- The asymptotic approximation `f(n) = log(n*sqrt(30))^3 / (6*log(2)*log(3)*log(5))`. -/
noncomputable def f (n : ℕ) : ℝ :=
  (Real.log ((n : ℝ) * Real.sqrt 30)) ^ 3 / (6 * Real.log 2 * Real.log 3 * Real.log 5)

theorem main :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → |(s n : ℝ) - f n| ≤ C * Real.log (Real.log (n : ℝ)) := by
  sorry

end OMA.S_oeis_a051037
