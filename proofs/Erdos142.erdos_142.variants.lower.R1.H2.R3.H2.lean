import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

open Real Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c d _ _ hc hd
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / d) c hc).comp
    ((tendsto_rpow_atTop hd).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop C] with N h
  dsimp at h
  rw [← rpow_mul (log_natCast_nonneg N), mul_div_cancel₀ _ hd.ne'] at h
  rwa [neg_mul, exp_neg, mul_inv_le_iff₀ (exp_pos _), one_div_mul_eq_div]
