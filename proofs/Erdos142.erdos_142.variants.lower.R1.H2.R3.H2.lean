import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! Shortens the power-times-exponential argument of PR #37229.
The earlier proofs appear in PRs #32292 and #36668. -/

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have hl := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp hl)).const_mul C
  filter_upwards [h.eventually_lt_const (by simp : C * 0 < 1), hl.eventually_gt_atTop 0] with n ht hn
  dsimp at *
  rw [← rpow_mul hn.le, mul_div_cancel₀ A hε.ne'] at ht
  rw [le_div_iff₀ (by positivity)]
  nlinarith
