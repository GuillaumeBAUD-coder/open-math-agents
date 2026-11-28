import OMAStatements.S_mo_195973
import Mathlib

/-!
MathOverflow 195973: following the answer of user44143, take a fair coin `X ∈ {0, 1}` and its
median `m = 1/2`. Then `E|X - m| = 1/2` and `E|X - X'| = 1/2`, so `c ≤ 1`.
-/

namespace OMA.P195973

open MeasureTheory ENNReal

/-- A fair coin with values `0` and `1`. -/
noncomputable def μ : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

lemma integral_μ (f : ℝ → ℝ) : ∫ x, f x ∂μ = (f 0 + f 1) / 2 := by
  rw [μ, integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]
  ring

instance : IsProbabilityMeasure μ := ⟨by
  simp [μ, Measure.add_apply]
  exact ENNReal.inv_two_add_inv_two⟩

lemma int_id : Integrable id μ :=
  ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
    (ENNReal.inv_ne_top.2 two_ne_zero)

lemma med1 : 2⁻¹ ≤ μ (Set.Iic (1 / 2 : ℝ)) := by
  simp [μ, Measure.add_apply, Measure.dirac_apply' _ measurableSet_Iic, Set.indicator]

lemma med2 : 2⁻¹ ≤ μ (Set.Ici (1 / 2 : ℝ)) := by
  simp [μ, Measure.add_apply, Measure.dirac_apply' _ measurableSet_Ici, Set.indicator]
  norm_num

lemma disproof_aux : ¬ (∃ c : ℝ, 1 < c ∧ ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      Integrable id μ → ∀ m : ℝ, 2⁻¹ ≤ μ (Set.Iic m) → 2⁻¹ ≤ μ (Set.Ici m) →
        c * ∫ x, |x - m| ∂μ ≤ ∫ x, ∫ y, |x - y| ∂μ ∂μ) := by
  rintro ⟨c, hc, h⟩
  have := h μ inferInstance int_id (1 / 2) med1 med2
  simp only [integral_μ] at this
  norm_num at this
  linarith

end OMA.P195973

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_195973.main) := OMA.P195973.disproof_aux
