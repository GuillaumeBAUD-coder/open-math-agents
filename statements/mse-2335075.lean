import Mathlib

/-!
# Are there any solvers to Chance Constrained Programming Problems?

Source: https://math.stackexchange.com/questions/2335075/are-there-any-solvers-to-chance-constrained-programming-problems (CC BY-SA 3.0)
Credit: @Bondyboy2001

The source asks whether scripts or solvers exist which turn chance constraints into deterministic
constraints by one of three listed methods. The literal existence of Matlab or Python software is
an empirical claim, not a mathematical proposition, and the source specifies no software interface.
The precise mathematical content fully stated in the source is the Gaussian reformulation: for
`ξ ∼ N(ξ̄, Σ)`, the linear chance constraint `P(ξᵀx ≥ b) ≤ ε` is equivalent to the deterministic
second-order-cone inequality `b - ξ̄ᵀx ≥ Φ⁻¹(1 - ε) ‖Σ^{1/2}x‖₂`. This file states that
equivalence, together with the convexity that makes the deterministic constraint tractable.

Formalization choices forced by boundary cases in the source:

* The linked Boyd notes state the second-order-cone form in the usual risk range `ε ≤ 1/2`,
  so that `Φ⁻¹(1 - ε) ≥ 0`; `main` uses the standard range `0 < ε ≤ 1/2`.
* The displayed equivalence is false without qualification when the one-dimensional Gaussian
  `ξᵀx` is degenerate. For example, at `x = 0` and `b = ξ̄ᵀx` the left side is false for
  `ε < 1` while the displayed right side is true. Accordingly `main` assumes the nondegeneracy
  condition `0 < xᵀΣx`.
* `Φ` is the cumulative distribution function of the standard real Gaussian measure. Since the
  Gaussian density is strictly positive, its inverse on `(0, 1)` is represented here by the usual
  quantile infimum.
* The scenario and Bernstein approximations are only sketched in the source. In particular the
  Bernstein formula is explicitly omitted there, so they are not replaced here by invented
  mathematical definitions.
-/

namespace OMA.S_mse_2335075

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

/-- The cumulative distribution function `Φ` of the standard Gaussian measure on `ℝ`. -/
noncomputable def standardNormalCdf (x : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) x

/-- The standard Gaussian quantile function `Φ⁻¹`, written as the quantile infimum. -/
noncomputable def standardNormalQuantile (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ standardNormalCdf x}

/-- The probability of the violation event `ξᵀx ≥ b` when
`ξ ∼ N(mean, covariance)`. -/
noncomputable def gaussianViolationProbability {n : ℕ}
    (mean : EuclideanSpace ℝ (Fin n)) (covariance : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (b : ℝ) : ℝ :=
  (multivariateGaussian mean covariance).real {ξ | b ≤ ⟪ξ, x⟫}

/-- The deterministic second-order-cone constraint produced by the Gaussian reformulation:
`Φ⁻¹(1 - ε) ‖Σ^{1/2}x‖₂ ≤ b - ξ̄ᵀx`. -/
noncomputable def gaussianSOCConstraint {n : ℕ}
    (mean : EuclideanSpace ℝ (Fin n)) (covariance : Matrix (Fin n) (Fin n) ℝ)
    (ε b : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  standardNormalQuantile (1 - ε) *
      ‖(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt covariance)) x‖ ≤
    b - ⟪mean, x⟫

/-- For a nondegenerate linear Gaussian constraint at a standard risk level, the chance
constraint is equivalent to its deterministic second-order-cone reformulation, and the feasible
set of that reformulation is convex. -/
theorem main :
    ∀ (n : ℕ) (mean : EuclideanSpace ℝ (Fin n)) (covariance : Matrix (Fin n) (Fin n) ℝ)
      (b ε : ℝ), covariance.PosSemidef → 0 < ε → ε ≤ 1 / 2 →
      Convex ℝ {x | gaussianSOCConstraint mean covariance ε b x} ∧
        ∀ x : EuclideanSpace ℝ (Fin n), 0 < x ⬝ᵥ covariance *ᵥ x →
          (gaussianViolationProbability mean covariance x b ≤ ε ↔
            gaussianSOCConstraint mean covariance ε b x) := by
  sorry

end OMA.S_mse_2335075
