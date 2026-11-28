import Mathlib

/-!
# A194348: sqrt(2)^sqrt(2)^sqrt(2) is transcendental

Source: https://oeis.org/A194348 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A194348: decimal expansion of sqrt(2)^sqrt(2)^sqrt(2) = 1.7608395558800280...

The entry records:

  If Schanuel's Conjecture is true, then sqrt(2)^sqrt(2)^sqrt(2) is transcendental (see
  Marques and Sondow 2010, p. 79).

The statement is the conjectured transcendence (the open question the entry points to).

Reading of the source:
* The power tower is grouped from the right, as usual: sqrt(2)^(sqrt(2)^sqrt(2)). This is the
  value of the decimal expansion (grouping from the left would give (sqrt(2)^sqrt(2))^sqrt(2) = 2).
  Powers are real powers (`Real.rpow`) of positive reals.
* "transcendental" means transcendental over ℚ (`Transcendental ℚ x`).
-/

namespace OMA.S_oeis_a194348

/-- `√2^√2^√2`, grouped from the right. -/
noncomputable def x : ℝ := Real.sqrt 2 ^ (Real.sqrt 2 ^ Real.sqrt 2)

/-- `√2^√2^√2` is transcendental. -/
theorem main : Transcendental ℚ x := by
  sorry

end OMA.S_oeis_a194348
