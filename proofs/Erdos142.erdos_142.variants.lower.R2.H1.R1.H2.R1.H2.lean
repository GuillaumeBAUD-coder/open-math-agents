import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

/- Shortens @MattGaiser (#35060). -/
open Real Filter in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have L := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Summable.of_norm_bounded_eventually_nat (summable_nat_pow_inv.2 one_lt_two) ?_
  filter_upwards [eventually_gt_atTop 0, L.eventually_gt_atTop 0,
    ((tendsto_rpow_atTop hη).comp L).eventually_ge_atTop (2 / c)] with j hj0 hl hp
  have hj : (0 : ℝ) < j := Nat.cast_pos.2 hj0
  have h4 : 1 ≤ log 4 := by
    rw [← log_exp 1]; exact log_le_log (exp_pos _) (exp_one_lt_d9.le.trans (by norm_num))
  have hg : log j ≤ log (log ((4 : ℝ) ^ j)) := by
    rw [log_pow]; exact log_le_log hj (le_mul_of_one_le_right hj.le h4)
  have h0 : 0 < log (log ((4 : ℝ) ^ j)) := hl.trans_le hg
  have h2 := (div_le_iff₀ hc).1 (hp.trans (rpow_le_rpow hl.le hg hη.le))
  rw [norm_of_nonneg (exp_pos _).le, ← exp_log (pow_pos hj 2), ← exp_neg, log_pow (j : ℝ) 2]
  refine exp_le_exp.2 ?_
  rw [rpow_add h0, rpow_one]
  dsimp at hl
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h2 h0.le]
