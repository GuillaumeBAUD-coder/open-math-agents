import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# MathOverflow 202502: Implication of MGF inequality

Source: https://mathoverflow.net/questions/202502/implication-of-mgf-inequality
Question by axk, 10 April 2015. Formalization credited to @etaubman.

The source asks whether ordering moment-generating functions for every positive
argument implies a direct inequality between the distribution tails. Here a
direct tail inequality means a uniform stochastic order at common thresholds.
We state the proposed implication even allowing either orientation of the order.
Its negation gives a pair whose CDFs cross despite the MGF order.

The measures are the laws of the real random variables. The MGF is written as
its defining integral. Integrability is explicit so that the integral cannot
take Lean's default value for a divergent integral. The CDF at x is the mass
of Iic x; comparing its ENNReal values is equivalent to comparing the usual
real CDFs for probability measures. No assumption on a common probability
space is needed, since every two laws can be realized on a product space.
-/

open MeasureTheory

namespace OMA.S_mo_202502

theorem main :
    ∀ μ ν : Measure ℝ,
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∀ t : ℝ, 0 < t →
        Integrable (fun x : ℝ => Real.exp (t * x)) μ ∧
        Integrable (fun x : ℝ => Real.exp (t * x)) ν ∧
        (∫ x : ℝ, Real.exp (t * x) ∂μ) ≤
          ∫ x : ℝ, Real.exp (t * x) ∂ν) →
      (∀ x : ℝ, μ (Set.Iic x) ≤ ν (Set.Iic x)) ∨
        (∀ x : ℝ, ν (Set.Iic x) ≤ μ (Set.Iic x)) := by
  sorry

end OMA.S_mo_202502
