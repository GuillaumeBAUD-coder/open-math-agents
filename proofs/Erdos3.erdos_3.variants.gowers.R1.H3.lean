import OMAReductions.R_Erdos3_erdos_3_variants_gowers_R1
import Mathlib

open Real Filter

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_gowers_R1.H3 := by
  intro c a hc ha
  have h := (isLittleO_log_rpow_atTop hc).bound (show 0 < a⁻¹ by positivity)
  filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  simp only [Real.norm_eq_abs,abs_of_nonneg (log_nonneg ht1.le),
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at ht
  rw [rpow_def_of_pos ht0 (-a)]
  apply exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left ht ha.le
  rw [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul] at this
  linarith
