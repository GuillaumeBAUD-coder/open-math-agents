import Mathlib

/-!
# A092035: Decimal expansion of (Pi/e)^2.

Source: https://oeis.org/A092035
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Equals 12*Sum_{k >= 1} ((-1)^(k+1)/k^2) * cos(sqrt(2*k^2*Pi^2/3 - 4)). Cf. A100074.
-/

namespace OMA.S_oeis_a092035

theorem main :
    (Real.pi / Real.exp 1) ^ 2 =
      12 * ∑' k : ℕ,
        ((-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ) ^ 2) *
          Real.cos (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * Real.pi ^ 2 / 3 - 4)) := by
  sorry

end OMA.S_oeis_a092035
