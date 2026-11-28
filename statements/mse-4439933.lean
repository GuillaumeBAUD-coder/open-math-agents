import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
/-!
# A formula for the generalized freshman derivative equation

Source: https://math.stackexchange.com/questions/4439933

For any given finite family g_i, put G = product g_i, D = product g_i',
and S = G'. The remaining factor satisfies the equation precisely when
f' (D - G) = f S. On an open interval where D - G is nonzero, the explicit
factor C exp (integral S / (D - G)) supplies a solution with initial value C.
The pointwise equivalence also covers the singular cases without division.
-/

namespace OMA.S_mse_4439933

noncomputable def product {n : ℕ} (g : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∏ i, g i x

noncomputable def derivativeProduct {n : ℕ} (dg : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∏ i, dg i x

noncomputable def productDerivative {n : ℕ}
    (g dg : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, g j x) * dg i x

noncomputable def rate {n : ℕ} (g dg : Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  productDerivative g dg x / (derivativeProduct dg x - product g x)

noncomputable def completingFactor {n : ℕ} (g dg : Fin n → ℝ → ℝ)
    (x₀ C x : ℝ) : ℝ :=
  C * Real.exp (∫ t in x₀..x, rate g dg t)

/-- The exact pointwise equation and the interval formula requested in the source. -/
theorem main :
    (∀ (n : ℕ) (g dg : Fin n → ℝ → ℝ) (f : ℝ → ℝ) (f' x : ℝ),
      (∀ i, HasDerivAt (g i) (dg i x) x) → HasDerivAt f f' x →
      (HasDerivAt (fun t => f t * product g t) (f' * derivativeProduct dg x) x ↔
        f' * (derivativeProduct dg x - product g x) = f x * productDerivative g dg x)) ∧
    (∀ (n : ℕ) (g dg : Fin n → ℝ → ℝ) (s : Set ℝ),
      IsOpen s → Set.OrdConnected s → ∀ (x₀ C : ℝ), x₀ ∈ s →
      (∀ i x, x ∈ s → HasDerivAt (g i) (dg i x) x) →
      (∀ i, ContinuousOn (dg i) s) →
      (∀ x ∈ s, derivativeProduct dg x - product g x ≠ 0) →
      completingFactor g dg x₀ C x₀ = C ∧
      ∀ x ∈ s,
        HasDerivAt (completingFactor g dg x₀ C)
          (completingFactor g dg x₀ C x * rate g dg x) x ∧
        HasDerivAt (fun t => completingFactor g dg x₀ C t * product g t)
          (deriv (completingFactor g dg x₀ C) x * derivativeProduct dg x) x) := by
  sorry

end OMA.S_mse_4439933
