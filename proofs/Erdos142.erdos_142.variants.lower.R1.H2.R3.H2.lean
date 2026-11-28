import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! Rescale to the standard limit of a power times an exponential. -/

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp hl)).const_mul C
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const zero_lt_one, hl.eventually_gt_atTop 0] with n ht hn
  dsimp at ht hn
  rw [← rpow_mul hn.le, show ε * (A / ε) = A by field_simp] at ht
  exact (le_div_iff₀ (rpow_pos_of_pos hn A)).2 (by nlinarith)
