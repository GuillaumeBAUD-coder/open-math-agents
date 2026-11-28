import OMAStatements.S_mo_195973

open MeasureTheory Set
open scoped ENNReal

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_195973.main) := by
  rintro ⟨c, hc, h⟩
  let μ : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)
  have hboth : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
    rw [← mul_two, ENNReal.inv_mul_cancel (by norm_num) (by simp)]
  have hprob : IsProbabilityMeasure μ := by
    simp [isProbabilityMeasure_iff, μ, Measure.smul_apply, Measure.add_apply, hboth]
  have hint : Integrable id μ :=
    (integrable_add_measure.mpr
      ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩).smul_measure (by simp)
  have hleft : (2 : ℝ≥0∞)⁻¹ ≤ μ (Iic 0) := by
    norm_num [μ, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply]
  have hright : (2 : ℝ≥0∞)⁻¹ ≤ μ (Ici 0) := by
    have hmass : μ (Ici 0) = 1 := by
      norm_num [μ, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply, hboth]
    rw [hmass]
    exact ENNReal.inv_le_one.mpr (by norm_num)
  have havg (f : ℝ → ℝ) : ∫ x, f x ∂μ = (f 0 + f 1) / 2 := by
    rw [show μ = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1) from rfl,
      integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
        (integrable_dirac (by simp)), integral_dirac, integral_dirac]
    simp [ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hineq := h μ hprob hint 0 hleft hright
  rw [havg, havg, havg (fun y ↦ |0 - y|), havg (fun y ↦ |1 - y|)] at hineq
  norm_num at hineq
  linarith
