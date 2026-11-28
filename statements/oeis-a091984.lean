import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

/-!
# OEIS A091984 — the proposed one-step stopping-time gap

Source: https://oeis.org/A091984
Credit: @ATLAS33137

We use the positive-argument series for Ei(log x), as in Hilliard's program
and worked example (the step from 2 goes to 1). The integral starting at 2
printed in the formula section would instead give zero at 2. Following the
question in the comment, the step from 1 to 0 counts for both iterations.
-/

namespace OMA.S_oeis_a091984

/-- The unoffset logarithmic integral on the inputs used by the recurrence. -/
noncomputable def li (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' k : ℕ, (Real.log x) ^ (k + 1) / ((k + 1 : ℝ) * (Nat.factorial (k + 1) : ℝ))

noncomputable def liStep (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⌊li n⌋₊

/-- The orbit reaches zero at step k for the first time. -/
def firstZero (f : ℕ → ℕ) (x k : ℕ) : Prop :=
  f^[k] x = 0 ∧ ∀ j < k, f^[j] x ≠ 0

/-- Hilliard's proposed gap for every positive decimal exponent. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ,
    firstZero Nat.primeCounting (10 ^ n) k ∧ firstZero liStep (10 ^ n) (k + 1) := by
  sorry

end OMA.S_oeis_a091984
