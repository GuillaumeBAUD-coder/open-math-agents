import Mathlib

/-!
# Sharpness of the Hardy–Littlewood bound for conjugate functions in `h^p`, `0 < p ≤ 1`

Source: https://mathoverflow.net/questions/450700/an-open-problem-of-hardy-and-littlewood-on-p-integral-means
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Hardy and Littlewood proved that if `u` is in the harmonic Hardy space `h^p` of the unit disc,
`0 < p ≤ 1`, then its harmonic conjugate `v` satisfies
`M_p(r, v) = O((log (1/(1-r)))^(1/p))` as `r → 1`, and that for `p = 1, 1/2, 1/3, …` the `O`
cannot be replaced by `o`. Duren records the other values of `p ∈ (0, 1]` as open. `main` states
that the bound is sharp for every `p ∈ (0, 1]`; a proof of its negation shows that for some `p`
the `O` can be improved to `o`.

Conventions:
* `u = Re f`, `v = Im f` with `f` holomorphic on the open unit disc and `Im f(0) = 0` (this is
  the harmonic conjugate normalised by `v(0) = 0`; every harmonic `u` on the disc arises so).
* `M_p(r, g)^p = (1/(2π)) ∫_0^{2π} |g(r e^{iθ})|^p dθ`. We work with `M_p^p`, so
  `M_p(r,v) = o((log (1/(1-r)))^(1/p))` becomes `M_p(r,v)^p = o(log (1/(1-r)))`.
* `u ∈ h^p` means `sup_{0 ≤ r < 1} M_p(r, u) < ∞`.
-/

namespace OMA.S_mo_450700

open Complex Filter

/-- `M_p(r, g)^p`, the `p`-th power of the integral mean of `g` on the circle of radius `r`. -/
noncomputable def meanPow (p r : ℝ) (g : ℂ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), |g ((r : ℂ) * exp ((θ : ℂ) * I))| ^ p

theorem main :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧ (f 0).im = 0 ∧
        BddAbove (Set.range fun r : Set.Ico (0 : ℝ) 1 => meanPow p r (fun z => (f z).re)) ∧
        ¬ ((fun r : ℝ => meanPow p r (fun z => (f z).im)) =o[nhdsWithin 1 (Set.Iio 1)]
            (fun r : ℝ => Real.log (1 / (1 - r)))) := by
  sorry

end OMA.S_mo_450700
