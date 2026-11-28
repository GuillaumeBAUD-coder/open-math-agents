import Mathlib

/-!
# A090469: Least distinct composite k with k + j*n composite for j = 1..n

Source: https://oeis.org/A090469
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Least (distinct) composite k such that k+n, k+2n, k+3n, ... up to n terms are
all composite.
Conjectures:
1. For n > 1, a(n) is the least composite k not already used such that gcd(n, k) > 1.
2. For any prime p > 5, a(p) = 2*p.
-/

namespace OMA.S_oeis_a090469

/-- Predicate that k is a composite natural number. -/
def isComposite (k : ℕ) : Prop :=
  1 < k ∧ ¬ Nat.Prime k

/-- 1-indexed sequence A090469 (with a 0 = 0). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    sInf {k : ℕ |
      isComposite k ∧
      (∀ i : Fin n, a (i.1 + 1) ≠ k) ∧
      (∀ j ∈ Finset.Icc 1 (n + 1), isComposite (k + j * (n + 1)))}
  decreasing_by all_goals (have := i.isLt; omega)

theorem main :
    (∀ n : ℕ, 1 < n →
      a n = sInf {k : ℕ | isComposite k ∧ (∀ i ∈ Finset.Ico 1 n, a i ≠ k) ∧ 1 < Nat.gcd n k}) ∧
    (∀ p : ℕ, Nat.Prime p → 5 < p → a p = 2 * p) := by
  sorry

end OMA.S_oeis_a090469
