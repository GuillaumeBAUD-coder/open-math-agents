import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1

/-! Apply the generalized Gaussian tail bound at half strength, then square it.
With x = log (j log 4), the squared exponential bound is an inverse square. -/

open Filter Real

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have h4 : 0 < log 4 := log_pos (by norm_num)
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const h4)
  have hg := (exp_neg_mul_rpow_isLittleO_exp_neg (half_pos hc) (show 1 < 1 + η by linarith)).bound one_pos
  refine Summable.of_norm_bounded_eventually_nat
    ((summable_one_div_nat_pow.mpr one_lt_two).div_const (log 4 ^ 2)) ?_
  filter_upwards [ht.eventually hg, eventually_gt_atTop 0] with j h hj
  have hp : 0 < (j : ℝ) * log 4 := mul_pos (by exact_mod_cast hj) h4
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (exp_pos _), one_mul,
    exp_neg, exp_log hp, abs_of_pos (inv_pos.mpr hp)] at h
  rw [norm_of_nonneg (exp_pos _).le, log_pow]
  calc
    _ = exp (-(c/2) * log ((j : ℝ) * log 4) ^ (1+η)) ^ 2 := by
      rw [sq, ← exp_add]; congr 1; ring
    _ ≤ ((j : ℝ) * log 4)⁻¹ ^ 2 := by gcongr
    _ = _ := by simp [mul_pow, div_eq_mul_inv]; ring
