import Mathlib

/-!
# A002448: Closed-form evaluation of Jacobi theta_4(exp(-Pi))

Source: https://oeis.org/A002448
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A002448: Expansion of Jacobi theta function theta_4(x).

Statement:
Conjecture: Sum_{k>=0} a(k) / exp(k*Pi) = (1/2)*Pi^(1/4)*2^(3/4)/Gamma(3/4).

Conventions:
- `theta_4(x) = 1 + 2 * Sum_{m>=1} (-1)^m * x^(m^2)`, so `a(0) = 1`, `a(m^2) = 2*(-1)^m`
  for `m >= 1`, and `a(k) = 0` otherwise.
-/

namespace OMA.S_oeis_a002448

/-- The `k`-th coefficient of the Jacobi theta function `theta_4(x)` (`A002448`). -/
def theta4Coeff (k : ℕ) : ℤ :=
  if k = 0 then 1
  else if (Nat.sqrt k) ^ 2 = k then 2 * (-1 : ℤ) ^ (Nat.sqrt k)
  else 0

theorem main :
    ∑' (k : ℕ), (theta4Coeff k : ℝ) / Real.exp ((k : ℝ) * Real.pi) =
      (1 / 2 : ℝ) * Real.pi ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((3 : ℝ) / 4) / Real.Gamma (3 / 4) := by
  sorry

end OMA.S_oeis_a002448
