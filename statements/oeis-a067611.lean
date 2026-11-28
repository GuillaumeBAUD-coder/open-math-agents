import Mathlib

/-!
# OEIS A067611: Numbers Not of the Form 6xy ± x ± y in Triangular Intervals

Source: https://oeis.org/A067611
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $S$ be the set of positive integers of the form $6xy \pm x \pm y$ for positive
integers $x, y \ge 1$, and let $T(k) = k(k + 1)/2$ be the $k$-th triangular number.

Conjecture 2 of the entry (2018):
For every $k \ge 2$, the interval $[T(k - 1) + 1, T(k)]$ contains at least one integer
not in $S$.
-/

namespace OMA.S_oeis_a067611

/-- `InA067611 m` holds when `m = 6xy ± x ± y` for some positive integers `x, y ≥ 1`. -/
def InA067611 (m : ℕ) : Prop :=
  ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧
    (m = 6 * x * y + x + y ∨
     m = 6 * x * y + x - y ∨
     m = 6 * x * y - x + y ∨
     m = 6 * x * y - x - y)

/-- The `k`-th triangular number `T(k) = k * (k + 1) / 2`. -/
def tri (k : ℕ) : ℕ :=
  k * (k + 1) / 2

theorem main :
    ∀ k : ℕ, 2 ≤ k → ∃ m : ℕ, tri (k - 1) + 1 ≤ m ∧ m ≤ tri k ∧ ¬ InA067611 m := by
  sorry

end OMA.S_oeis_a067611
