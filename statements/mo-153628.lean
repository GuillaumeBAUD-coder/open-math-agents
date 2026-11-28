import Mathlib

/-!
# Is an atomless natural exponential family whose members have median = mean Gaussian?

Source: https://mathoverflow.net/questions/153628
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 153628, Georges Henry, Jan 2014): let `m` be a positive measure on the
real line. Assume that `exp k(t) = ∫ exp(xt) m(dx) < ∞` for `a < t < b` and `exp k(t) = ∞` if
`t ∉ [a, b]`, with `-∞ ≤ a < b ≤ ∞`. Then `P_t(dx) = exp(xt - k(t)) m(dx)` is a probability for
`t ∈ (a, b)` with `k'(t) = ∫ x P_t(dx)`. Assume that `m` has no atoms and that for all `t ∈ (a, b)`,
`1/2 = P_t((-∞, k'(t)))`. Is it true that `P_t` is Gaussian? The page has no answer; `main`
states the affirmative answer, for every `t ∈ (a, b)`.

Modelling choices:
* `a, b : EReal` with `a < b`, so that `a = -∞` and `b = ∞` are allowed. Finiteness is required
  for real `t` with `a < t < b`, and infiniteness for real `t` with `t < a` or `b < t`; nothing is
  assumed at the endpoints, as in the source.
* `k(t) = log (∫ exp(xt) m(dx))` (the integral is the lower Lebesgue integral, finite on `(a, b)`),
  `P_t = m.withDensity (x ↦ exp(xt - k(t)))`, and `k'(t)` is `deriv k t`. The facts that `P_t` is a
  probability and `k'(t)` is its mean are consequences in the source, not extra hypotheses.
* "`m` has no atoms" is `NullSingletonClass m` (every singleton is `m`-null). "`P_t` is Gaussian" means `P_t = gaussianReal μ v` for some
  mean `μ` and some variance `v ≠ 0` (a non-degenerate normal law; a Dirac mass is impossible here
  since `m` has no atoms).
-/

namespace OMA.S_mo_153628

open MeasureTheory ProbabilityTheory

/-- The Laplace transform `t ↦ ∫ exp(xt) m(dx)` of `m`, in `[0, ∞]`. -/
noncomputable def laplace (m : Measure ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (x * t)) ∂m

/-- The cumulant function `k(t) = log ∫ exp(xt) m(dx)` (meaningful where the integral is finite). -/
noncomputable def k (m : Measure ℝ) (t : ℝ) : ℝ := Real.log (laplace m t).toReal

/-- The member `P_t(dx) = exp(xt - k(t)) m(dx)` of the natural exponential family. -/
noncomputable def P (m : Measure ℝ) (t : ℝ) : Measure ℝ :=
  m.withDensity fun x => ENNReal.ofReal (Real.exp (x * t - k m t))

/-- **MathOverflow 153628 (affirmative answer).** If `m` has no atoms and every `P_t`,
`t ∈ (a, b)`, gives mass `1/2` to `(-∞, k'(t))`, then every `P_t` is Gaussian. -/
theorem main :
    ∀ (m : Measure ℝ) (a b : EReal), a < b →
      (∀ t : ℝ, a < t → (t : EReal) < b → laplace m t < ⊤) →
      (∀ t : ℝ, ((t : EReal) < a ∨ b < t) → laplace m t = ⊤) →
      NullSingletonClass m →
      (∀ t : ℝ, a < t → (t : EReal) < b → P m t (Set.Iio (deriv (k m) t)) = 1 / 2) →
      ∀ t : ℝ, a < t → (t : EReal) < b →
        ∃ (μ : ℝ) (v : NNReal), v ≠ 0 ∧ P m t = gaussianReal μ v := by
  sorry

end OMA.S_mo_153628
