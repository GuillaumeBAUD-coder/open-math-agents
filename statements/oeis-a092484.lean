import Mathlib

/-!
# A092484: Expansion of Product_{m>=1} (1 + m^2*q^m).

Source: https://oeis.org/A092484
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: log(a(n)) ~ sqrt(2*n) * (log(2*n) - 2).
-/

namespace OMA.S_oeis_a092484

def a (n : ℕ) : ℕ :=
  ∑ s ∈ (Finset.Icc 1 n).powerset.filter (fun s => s.sum id = n), ∏ m ∈ s, m ^ 2

theorem main :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => Real.log (a n : ℝ))
      (fun n : ℕ => Real.sqrt (2 * (n : ℝ)) * (Real.log (2 * (n : ℝ)) - 2)) := by
  sorry

end OMA.S_oeis_a092484
