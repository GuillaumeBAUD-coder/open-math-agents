import Mathlib

/-!
# A004405: Expansion of 1 / (Sum_{n=-oo..oo} x^(n^2))^4

Source: https://oeis.org/A004405
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
  Sum_{k >= 0} a(k) / exp(k * Pi) = (1 / Pi) * Gamma(3/4)^4,
where Sum_{k >= 0} a(k) * x^k = 1 / theta_3(x)^4 and theta_3(x) = Sum_{m in ℤ} x^(m^2).
-/

namespace OMA.S_oeis_a004405

open Classical

/-- Coefficient of x^n in theta_3(x) = 1 + 2 * Sum_{m >= 1} x^(m^2). -/
noncomputable def theta3Coeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else if IsSquare n then 2 else 0

/-- Coefficient of x^n in theta_3(x)^2. -/
noncomputable def r2 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), theta3Coeff k * theta3Coeff (n - k)

/-- Coefficient of x^n in theta_3(x)^4. -/
noncomputable def r4 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), r2 k * r2 (n - k)

/-- Coefficient of x^n in 1 / theta_3(x)^4, defined recursively since r4(0) = 1. -/
noncomputable def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => - ∑ k : Fin (n + 1), a k.1 * r4 (n + 1 - k.1)

/-- Conjecture: Sum_{k >= 0} a(k) / exp(k * Pi) = Gamma(3/4)^4 / Pi. -/
theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) / Real.exp ((k : ℝ) * Real.pi))
      ((1 / Real.pi) * (Real.Gamma (3 / 4)) ^ 4) := by
  sorry

end OMA.S_oeis_a004405
