import Mathlib

/-!
# A193178: (1/2)^(1/2)^(1/2)^(1/2) is transcendental

Source: https://oeis.org/A193178 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A193178: decimal expansion of (1/2)^(1/2)^(1/2)^(1/2) = 0.6540408600420694...

The entry records:

  A weak form of Schanuel's Conjecture implies that (1/2)^(1/2)^(1/2)^(1/2) is
  transcendental--see Marques and Sondow (2012).

The statement is the conjectured transcendence (the open question the entry points to).

Reading of the source:
* The power tower is grouped from the right, as usual: (1/2)^((1/2)^((1/2)^(1/2))). This is the
  value of the decimal expansion (grouping from the left would give 0.5^(0.5^3) = 0.917...).
  Powers are real powers (`Real.rpow`) of positive reals.
* "transcendental" means transcendental over ℚ (`Transcendental ℚ x`).
-/

namespace OMA.S_oeis_a193178

/-- `(1/2)^(1/2)^(1/2)^(1/2)`, grouped from the right. -/
noncomputable def x : ℝ := (1 / 2 : ℝ) ^ ((1 / 2 : ℝ) ^ ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)))

/-- `(1/2)^(1/2)^(1/2)^(1/2)` is transcendental. -/
theorem main : Transcendental ℚ x := by
  sorry

end OMA.S_oeis_a193178
