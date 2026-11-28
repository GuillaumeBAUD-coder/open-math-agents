import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

/-! Summability by eventual comparison with a scaled inverse square. -/

open Filter Real

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have h := tendsto_natCast_atTop_atTop.atTop_mul_const (log_pos (by norm_num : 1 < (4 : ℝ)))
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_one_div_nat_pow.mpr one_lt_two).div_const (log 4 ^ 2)) ?_
  filter_upwards [h.eventually_gt_atTop 1,
    (((tendsto_rpow_atTop hη).comp (tendsto_log_atTop.comp h)).const_mul_atTop hc).eventually_ge_atTop 2]
    with j hj hb
  simp only [Function.comp_apply] at hb
  rw [norm_of_nonneg (exp_pos _).le, log_pow, add_comm 1, rpow_add_one (log_pos hj).ne']
  calc
    _ ≤ exp (-(2 * log ((j : ℝ) * log 4))) := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hb (log_pos hj).le]
    _ = _ := by
      rw [exp_neg, two_mul, exp_add, exp_log (zero_lt_one.trans hj), ← sq, mul_pow]
      simp [div_eq_mul_inv] <;> ring
