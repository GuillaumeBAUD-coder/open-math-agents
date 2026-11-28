import Mathlib

/-!
# A014972: Expansion of (theta3(q) / theta4(q))^4 in powers of q

Source: https://oeis.org/A014972
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
Let `a(k)` be the coefficient of `q^k` in `(θ₃(q) / θ₄(q))^4`, where
`θ₃(q) = 1 + 2 * ∑_{n ≥ 1} q^(n^2)` and `θ₄(q) = 1 + 2 * ∑_{n ≥ 1} (-1)^n * q^(n^2)`.
Then `∑_{k ≥ 0} a(k) / exp(k * π) = 2`.

Conventions:
- `theta3` and `theta4` are defined as formal power series in `PowerSeries ℤ`.
- The sequence `a(k)` is the coefficient sequence of `f : PowerSeries ℤ` satisfying
  `theta4 ^ 4 * f = theta3 ^ 4`.
-/

namespace OMA.S_oeis_a014972

noncomputable def theta3 : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    if k = 0 then 1 else if IsSquare k then 2 else 0

noncomputable def theta4 : PowerSeries ℤ :=
  PowerSeries.mk fun k =>
    if k = 0 then 1 else if IsSquare k then 2 * (-1 : ℤ) ^ Nat.sqrt k else 0

theorem main :
    ∀ f : PowerSeries ℤ,
      theta4 ^ 4 * f = theta3 ^ 4 →
      HasSum (fun k : ℕ => ((PowerSeries.coeff k f : ℤ) : ℝ) / Real.exp ((k : ℝ) * Real.pi)) 2 := by
  sorry

end OMA.S_oeis_a014972
