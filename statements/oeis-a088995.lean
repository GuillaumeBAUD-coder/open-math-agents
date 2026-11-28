import Mathlib

/-!
# A088995: Least k > 0 such that the first n digits of 2^k and 5^k are identical

Source: https://oeis.org/A088995
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Least k > 0 such that the first n digits of 2^k and 5^k are identical.
Conjecture: log(a(n)/10^n) = O(log log n).
-/

namespace OMA.S_oeis_a088995

/-- Predicate asserting that 2^k and 5^k each have at least n base-10 digits and
agree on their n most significant digits. -/
def sameFirstDigits (n k : ℕ) : Prop :=
  n ≤ (Nat.digits 10 (2 ^ k)).length ∧
  n ≤ (Nat.digits 10 (5 ^ k)).length ∧
  (Nat.digits 10 (2 ^ k)).reverse.take n = (Nat.digits 10 (5 ^ k)).reverse.take n

/-- a(n) = least k > 0 such that the first n digits of 2^k and 5^k are identical. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ sameFirstDigits n k}

theorem main :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => Real.log ((a n : ℝ) / (10 : ℝ) ^ n))
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) := by
  sorry

end OMA.S_oeis_a088995
