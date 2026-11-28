import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Original proof: Raimo33.
/-! A stretched exponential eventually dominates every fixed logarithmic power. -/

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ hC hc hε
  have L := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have T := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp L)
  filter_upwards [T.eventually_lt_const (inv_pos.mpr hC), L.eventually_gt_atTop 0] with n hn hl
  simp only [Function.comp_apply] at hl
  rw [le_div_iff₀ (rpow_pos_of_pos hl A)]
  simp only [Function.comp_apply, ← rpow_mul hl.le, mul_div_cancel₀ _ hε.ne'] at hn
  nlinarith [mul_lt_mul_of_pos_left hn hC, mul_inv_cancel₀ hC.ne']
