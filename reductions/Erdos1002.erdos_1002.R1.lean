import FormalConjectures.ErdosProblems.«1002»
import Mathlib

/-!
# Erdős 1002: separate the Fourier input from probabilistic transport

The affirmative argument for Erdős Problem 1002 has two different kinds of input.
The analytic number-theoretic core is convergence of the characteristic functions of
the normalized rotation sums to those of the centered Cauchy law of scale `1/(2π)`.
The probabilistic transport step turns that Fourier convergence into convergence of the
distribution functions.  The remaining pieces are the endpoint properties of the Cauchy
distribution and the measure-theoretic identification of the finite-sample laws with
the volume formulation in the catalogue statement.
-/

open Filter Finset MeasureTheory Set
open scoped Topology NNReal

namespace OMA.R_Erdos1002_erdos_1002_R1

/-- Fourier input: the characteristic functions of the finite normalized rotation-sum
laws converge pointwise to those of the centered Cauchy law of scale `1/(2π)`. -/
def H1 : Prop :=
  let f : ℝ → ℕ → ℝ := fun α n ↦
    (1 / Real.log n) * ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))
  let γ : ℝ≥0 := ⟨(2 * Real.pi)⁻¹, by positivity⟩
  ∀ t : ℝ,
    Tendsto
      (fun n : ℕ ↦ charFun ((volume.restrict (Ioo (0 : ℝ) 1)).map (fun α ↦ f α n)) t)
      atTop (𝓝 (charFun (ProbabilityTheory.cauchyMeasure 0 γ) t))

/-- Lévy transport: the preceding characteristic-function convergence implies convergence
of the finite distribution functions to the Cauchy distribution function at every real
threshold. -/
def H2 : Prop :=
  let f : ℝ → ℕ → ℝ := fun α n ↦
    (1 / Real.log n) * ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))
  let γ : ℝ≥0 := ⟨(2 * Real.pi)⁻¹, by positivity⟩
  (∀ t : ℝ,
    Tendsto
      (fun n : ℕ ↦ charFun ((volume.restrict (Ioo (0 : ℝ) 1)).map (fun α ↦ f α n)) t)
      atTop (𝓝 (charFun (ProbabilityTheory.cauchyMeasure 0 γ) t))) →
  ∀ c : ℝ,
    Tendsto
      (fun n : ℕ ↦
        (((volume.restrict (Ioo (0 : ℝ) 1)).map (fun α ↦ f α n)) (Iic c)).toReal)
      atTop (𝓝 (((ProbabilityTheory.cauchyMeasure 0 γ) (Iic c)).toReal))

/-- The centered Cauchy law of scale `1/(2π)` has a monotone distribution function with
the correct endpoint limits. -/
def H3 : Prop :=
  let γ : ℝ≥0 := ⟨(2 * Real.pi)⁻¹, by positivity⟩
  let g : ℝ → ℝ := fun c ↦ (((ProbabilityTheory.cauchyMeasure 0 γ) (Iic c)).toReal)
  Monotone g ∧ Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 1)

/-- Measure accounting: the volume of rotation sums below a threshold in the unit interval
is the value of the corresponding pushforward law on `Iic`. -/
def H4 : Prop :=
  let f : ℝ → ℕ → ℝ := fun α n ↦
    (1 / Real.log n) * ∑ k ∈ Icc (1 : ℕ) n, (1 / 2 - Int.fract (α * k))
  ∀ c : ℝ, ∀ n : ℕ,
    (volume { α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ f α n ≤ c }).toReal =
      (((volume.restrict (Ioo (0 : ℝ) 1)).map (fun α ↦ f α n)) (Iic c)).toReal

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos1002.erdos_1002 := by
  intro h1 h2 h3 h4
  let γ : ℝ≥0 := ⟨(2 * Real.pi)⁻¹, by positivity⟩
  let g : ℝ → ℝ := fun c ↦ (((ProbabilityTheory.cauchyMeasure 0 γ) (Iic c)).toReal)
  have hg : Monotone g ∧ Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 1) := h3
  refine ⟨g, hg.1, hg.2.1, hg.2.2, ?_⟩
  intro c
  have hcdf := h2 h1 c
  exact hcdf.congr' (Filter.Eventually.of_forall fun n ↦ (h4 c n).symm)

end OMA.R_Erdos1002_erdos_1002_R1
