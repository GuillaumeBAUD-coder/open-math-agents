import Mathlib

/-!
# A004403: Expansion of 1/theta_3(q)^2 in powers of q

Source: https://oeis.org/A004403
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
  Sum_{k >= 0} a(k) / exp(k * Pi) = (1 / Pi^(1/2)) * Gamma(3/4)^2,
where Sum_{k >= 0} a(k) * q^k = 1 / theta_3(q)^2 and theta_3(q) = Sum_{m in ℤ} q^(m^2).
-/

namespace OMA.S_oeis_a004403

open Classical

/-- Coefficient of q^n in theta_3(q) = 1 + 2 * Sum_{m >= 1} q^(m^2). -/
noncomputable def theta3Coeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else if IsSquare n then 2 else 0

/-- Coefficient of q^n in theta_3(q)^2. -/
noncomputable def r2 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), theta3Coeff k * theta3Coeff (n - k)

/-- Coefficient of q^n in 1 / theta_3(q)^2, defined recursively since r2(0) = 1. -/
noncomputable def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => - ∑ k : Fin (n + 1), a k.1 * r2 (n + 1 - k.1)

/-- Conjecture: Sum_{k >= 0} a(k) / exp(k * Pi) = Gamma(3/4)^2 / sqrt(Pi). -/
theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) / Real.exp ((k : ℝ) * Real.pi))
      ((1 / Real.sqrt Real.pi) * (Real.Gamma (3 / 4)) ^ 2) := by
  sorry

end OMA.S_oeis_a004403
