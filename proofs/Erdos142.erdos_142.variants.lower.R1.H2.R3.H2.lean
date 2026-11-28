import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! This proof uses the comparison from the merged proof at commit fdbd3e696.
Clearing the reciprocal of the exponential gives the inequality directly. -/

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have L := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp L)).eventually_ge_atTop C,
    L.eventually_gt_atTop 0] with N h hN
  rw [neg_mul, exp_neg, mul_inv_le_iff₀ (exp_pos _), one_div, inv_mul_eq_div]
  simp only [Function.comp] at h
  change 0 < log (N : ℝ) at hN
  rwa [← rpow_mul hN.le, show ε * (A / ε) = A by field_simp] at h
