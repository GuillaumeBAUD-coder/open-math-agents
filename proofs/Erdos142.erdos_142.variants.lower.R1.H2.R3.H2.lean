import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! Use the limit of a power times a decaying exponential at the changed variable. -/

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have L := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / ε) c hc).mul_const C
  rw [zero_mul] at h
  filter_upwards [(h.comp ((tendsto_rpow_atTop hε).comp L)).eventually
    (gt_mem_nhds zero_lt_one), L.eventually_gt_atTop 0] with N hN hL
  dsimp at hN hL
  apply (le_div_iff₀ (rpow_pos_of_pos hL A)).2
  rw [← rpow_mul hL.le, show ε * (A / ε) = A by field_simp] at hN
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hN.le
