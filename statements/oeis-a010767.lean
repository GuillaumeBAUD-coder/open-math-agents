import Mathlib

/-!
# Plouffe's series for the fourth root of 2 (A010767)

Source: https://oeis.org/A010767
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Plouffe, 2025): `2^(1/4) = Σ_{k ≥ 0} A007096(k) / exp(k π)`, where A007096 is the
expansion of `θ₃ / θ₄`. (Bala's comment in the entry sketches a proof via eta quotients.)

Conventions:
* `θ₃(q) = Σ_{n ∈ ℤ} q^(n²)`, so its `n`-th coefficient is the number of integers `m` with
  `m² = n`; `θ₄(q) = θ₃(-q)` has `n`-th coefficient `(-1)^n` times that.
* A007096 is the coefficient sequence of the formal power series `θ₃ · θ₄⁻¹` over `ℝ`
  (`θ₄` has constant term 1, so it is invertible).
* The identity is stated as `HasSum`.
-/

namespace OMA.S_oeis_a010767

/-- Coefficients of `θ₃`. -/
def t3 (n : ℕ) : ℝ := if n = 0 then 1 else if Nat.sqrt n * Nat.sqrt n = n then 2 else 0

/-- A007096(k), the `k`-th coefficient of `θ₃ / θ₄`. -/
noncomputable def A007096 (k : ℕ) : ℝ :=
  PowerSeries.coeff k (PowerSeries.mk t3 * (PowerSeries.mk fun n => (-1) ^ n * t3 n)⁻¹)

theorem main :
    HasSum (fun k : ℕ => A007096 k / Real.exp (k * Real.pi)) ((2 : ℝ) ^ ((1 : ℝ) / 4)) := by
  sorry

end OMA.S_oeis_a010767
