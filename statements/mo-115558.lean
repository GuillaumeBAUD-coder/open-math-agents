import Mathlib.Data.Real.Basic

namespace OMA.S_mo_115558

/-- The strip in the question. -/
def InDomain (c : ℝ) (z : ℝ × ℝ) : Prop :=
  0 ≤ z.1 ∧ z.1 ≤ c ∧ 0 ≤ z.2

noncomputable def ratio (c : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 / (c + z.2)

/-- A convex piecewise-linear function is a maximum of affine functions.
Repeated pieces allow fewer than `k` pieces. -/
def MaxOfAffine (k : ℕ) (g : ℝ × ℝ → ℝ) : Prop :=
  ∃ a b d : Fin k → ℝ, ∀ z : ℝ × ℝ,
    (∀ i, a i * z.1 + b i * z.2 + d i ≤ g z) ∧
    (∃ i, g z = a i * z.1 + b i * z.2 + d i)

/-- Upper bounds and optimality are both compared pointwise on the strip. -/
def IsLeastMajorant (c : ℝ) (k : ℕ) (g : ℝ × ℝ → ℝ) : Prop :=
  MaxOfAffine k g ∧ (∀ z, InDomain c z → ratio c z ≤ g z) ∧
    ∀ h : ℝ × ℝ → ℝ, MaxOfAffine k h →
      (∀ z, InDomain c z → ratio c z ≤ h z) →
        ∀ z, InDomain c z → g z ≤ h z

/-- The pointwise optimum for a prescribed upper bound on the number of affine pieces. -/
theorem main :
    ∀ c : ℝ, 0 < c →
      IsLeastMajorant c 1 (fun z => z.1 / c) ∧
      (∀ k : ℕ, 2 ≤ k → ¬ ∃ g : ℝ × ℝ → ℝ, IsLeastMajorant c k g) := by
  sorry

end OMA.S_mo_115558
