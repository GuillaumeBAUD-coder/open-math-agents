import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

open Real
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually_ge_atTop C] with N h
  simp at h
  rw [← rpow_mul (by positivity)] at h
  simp [exp_neg]
  field_simp at *
  exact h
