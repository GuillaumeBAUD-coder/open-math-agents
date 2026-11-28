import Mathlib

/-!
# Stochastic dominance `tanh Y · tanh Z ⪰ tanh X` for Gaussians with mean = variance

Source: https://mathoverflow.net/questions/505921
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 505921, Dec 2025): let `X, Y, Z` be independent Gaussian random
variables with mean = variance, with parameters `g_X, g_Y, g_Z > 0`; set `U := tanh X`,
`V := tanh Y tanh Z`. Given `g_Y, g_Z > 0`, is there `g_X > 0` (depending on `g_Y, g_Z`) such that
`tanh Y tanh Z ⪰_st tanh X`, that is `F_U(t) ≥ F_V(t)` for every `t ∈ (-1, 1)`, where
`F_T(t) = P(T ≤ t)`? (The asker confirmed in a comment that it is mean = variance, not mean =
standard deviation.) The page has no answer; `main` states the affirmative answer.

Modelling choices:
* `X ∼ N(g_X, g_X)`, i.e. `gaussianReal g_X g_X` with the variance as an element of `ℝ≥0`.
* Since `F_U` depends only on the law of `X` and `F_V` only on the joint law of the independent
  pair `(Y, Z)`, the probabilities are written with laws directly: `F_U(t)` is the
  `gaussianReal g_X g_X`-measure of `{x | tanh x ≤ t}`, and `F_V(t)` is the product measure
  `gaussianReal g_Y g_Y ⊗ gaussianReal g_Z g_Z` of `{(y, z) | tanh y * tanh z ≤ t}`.
-/

namespace OMA.S_mo_505921

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **MathOverflow 505921 (affirmative answer).** For all `g_Y, g_Z > 0` there is `g_X > 0` with
`P(tanh X ≤ t) ≥ P(tanh Y tanh Z ≤ t)` for all `t ∈ (-1, 1)`. -/
theorem main :
    ∀ gY gZ : ℝ≥0, 0 < gY → 0 < gZ →
      ∃ gX : ℝ≥0, 0 < gX ∧
        ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
          ((gaussianReal gY gY).prod (gaussianReal gZ gZ))
              {p : ℝ × ℝ | Real.tanh p.1 * Real.tanh p.2 ≤ t} ≤
            gaussianReal gX gX {x : ℝ | Real.tanh x ≤ t} := by
  sorry

end OMA.S_mo_505921
