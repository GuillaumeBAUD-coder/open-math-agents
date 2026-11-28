import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib

/-! An inverse-square comparison for the log-power series. -/

open Filter Real

-- Compare with the inverse-square series once the log-power reaches 2/c.
-- The merged proof by MattGaiser uses the same comparison.
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hlog : Tendsto (fun j : ℕ => log (j : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Summable.of_norm_bounded_eventually_nat (g := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹)
    (summable_nat_pow_inv.mpr one_lt_two) ?_
  have h4 : 1 ≤ log 4 :=
    (le_log_iff_exp_le (by norm_num)).mpr (by linarith [exp_one_lt_d9])
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlog.eventually_gt_atTop 0,
    ((tendsto_rpow_atTop hη).comp hlog).eventually_ge_atTop (2 / c)] with j hj hjlog hlarge
  have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
  have hle : log (j : ℝ) ≤ log (log ((4 : ℝ) ^ j)) := by
    rw [log_pow]
    exact log_le_log hj' (le_mul_of_one_le_right hj'.le h4)
  have h := (div_le_iff₀ hc).mp (hlarge.trans (rpow_le_rpow hjlog.le hle hη.le))
  have hsq : log ((j : ℝ) ^ 2) = 2 * log (j : ℝ) := by norm_num [log_pow]
  rw [norm_of_nonneg (exp_pos _).le, ← exp_log (show 0 < (j : ℝ) ^ 2 by positivity),
    ← exp_neg, exp_le_exp, hsq, rpow_add (hjlog.trans_le hle), rpow_one]
  nlinarith [mul_le_mul_of_nonneg_left h (hjlog.trans_le hle).le]
