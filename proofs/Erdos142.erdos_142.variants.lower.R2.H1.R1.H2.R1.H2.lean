import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

open Filter Real

/-! P-series comparison at j * log 4, following the argument of reduction #29901. -/
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hbase : 0 < log 4 := log_pos (by norm_num)
  have scale : Tendsto (fun j : ℕ => (j : ℝ) * log 4) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hbase).2 tendsto_natCast_atTop_atTop
  have logs := tendsto_log_atTop.comp scale
  have powers := (tendsto_rpow_atTop hη).comp logs
  have series : Summable (fun j : ℕ => ((j : ℝ) * log 4) ^ (-2 : ℝ)) := by
    simpa only [mul_rpow (Nat.cast_nonneg _) hbase.le] using
      (summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_right (log 4 ^ (-2 : ℝ))
  apply series.of_norm_bounded_eventually_nat
  filter_upwards [scale.eventually_gt_atTop 0, logs.eventually_gt_atTop 0,
    powers.eventually_ge_atTop (2 / c)] with j hj hl hp
  change 0 < log ((j : ℝ) * log 4) at hl
  change 2 / c ≤ log ((j : ℝ) * log 4) ^ η at hp
  rw [norm_of_nonneg (exp_pos _).le, log_pow, rpow_def_of_pos hj, exp_le_exp,
    rpow_add hl, rpow_one]
  nlinarith only [mul_le_mul_of_nonneg_left ((div_le_iff₀ hc).mp hp) hl.le]
