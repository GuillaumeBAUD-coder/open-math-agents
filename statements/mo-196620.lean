import Mathlib

/-!
# Stability of Rényi entropy and divergence at order one

Source: https://mathoverflow.net/questions/196620

The question asks about upper domination of a varying probability density
when the Rényi order also tends to one. Finite integrals of two powers on
either side of one specify the regularity used for entropy convergence.
With the reference density fixed, the same condition applies to the
likelihood ratio under the reference measure. The proposed analogous
claim for a varying reference density fails even on the unit interval.
The sequence formulation expresses the limits in the question.
-/

namespace OMA.S_mo_196620

open MeasureTheory Filter Topology Set
open scoped ENNReal

universe u

/-- A nonnegative measurable density with total mass one. -/
structure IsDensity {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop where
  measurable : Measurable f
  nonneg : ∀ x, 0 ≤ f x
  integrable : Integrable f μ
  integral_eq_one : (∫ x, f x ∂μ) = 1

/-- A sequence of positive Rényi orders tending to one through values other than one. -/
def ApproachesOne (a : ℕ → ℝ) : Prop :=
  Tendsto a atTop (𝓝 1) ∧ ∀ n, 0 < a n ∧ a n ≠ 1

/-- One-sided control of the density ratios. -/
def UpperDomination {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (F : ℕ → Ω → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧ ∀ n, ∀ᵐ x ∂μ, F n x ≤ c n * f x

/-- Finite powers on either side of order one. -/
def NearbyMoments {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ Integrable (fun x => f x ^ (1 - δ)) μ ∧
    Integrable (fun x => f x ^ (1 + δ)) μ

/-- Rényi entropy with the sign convention of the question. -/
noncomputable def renyiEntropy {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (f : Ω → ℝ) : ℝ :=
  Real.log (∫ x, f x ^ a ∂μ) / (a - 1)

noncomputable def renyiDivergence {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (f g : Ω → ℝ) : ℝ :=
  Real.log (∫ x, f x ^ a * g x ^ (1 - a) ∂μ) / (a - 1)

noncomputable def referenceMeasure {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (g x))

def EntropyStability : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (F : ℕ → Ω → ℝ) (a : ℕ → ℝ),
    IsDensity μ f → (∀ n, IsDensity μ (F n)) → ApproachesOne a →
    UpperDomination μ f F → NearbyMoments μ f →
      Tendsto (fun n => renyiEntropy μ (a n) (F n)) atTop (𝓝 (∫ x, f x * Real.log (f x) ∂μ))

def FirstArgumentStability : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (F : ℕ → Ω → ℝ) (a : ℕ → ℝ),
    IsDensity μ f → IsDensity μ g → (∀ᵐ x ∂μ, g x = 0 → f x = 0) →
    (∀ n, IsDensity μ (F n)) →
    ApproachesOne a → UpperDomination μ f F →
    NearbyMoments (referenceMeasure μ g) (fun x => f x / g x) →
      Tendsto (fun n => renyiDivergence μ (a n) (F n) g) atTop
        (𝓝 (∫ x, f x * Real.log (f x / g x) ∂μ))

noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

def SecondArgumentCounterexample : Prop :=
  ∃ (a : ℕ → ℝ) (G : ℕ → ℝ → ℝ),
    ApproachesOne a ∧ (∀ n, 1 < a n) ∧ (∀ n, IsDensity unitIntervalMeasure (G n)) ∧
    (∀ n x, 0 < G n x) ∧ UpperDomination unitIntervalMeasure (fun _ => 1) G ∧
    (∀ n, Integrable (fun x => G n x ^ (1 - a n)) unitIntervalMeasure) ∧
    Tendsto (fun n => renyiDivergence unitIntervalMeasure (a n) (fun _ => 1) (G n)) atTop atTop

end OMA.S_mo_196620

namespace OMA.S_mo_196620

universe u

theorem main :
    EntropyStability.{u} ∧ FirstArgumentStability.{u} ∧ SecondArgumentCounterexample := by
  sorry

end OMA.S_mo_196620
