import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

/-!
Step H2 of the reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2: the stretched exponential C exp(-c (j log 4)^e) is summable.

Since log x = o(x^e), for large j we have log (j log 4) <= (c / 2) (j log 4)^e, and
log j <= log (j log 4) because log 4 >= 1. Hence the term is at most C / j^2.
-/

open Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e hC hc he
  have hs : Summable (fun j : ℕ => C * ((1 : ℝ) / (j : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left C
  refine hs.of_norm_bounded_eventually_nat ?_
  have hl4 : 1 ≤ Real.log 4 := by
    have h : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) h
  have hlo := (isLittleO_log_rpow_atTop he).def (show (0 : ℝ) < c / 2 by positivity)
  have hcast : Tendsto (fun j : ℕ => (j : ℝ) * Real.log 4) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
  filter_upwards [eventually_gt_atTop 0, hcast.eventually hlo, hcast.eventually_ge_atTop 1]
    with j hj hlog hge1
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hx : 0 < (j : ℝ) * Real.log 4 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  rw [Real.norm_of_nonneg (Real.log_nonneg hge1),
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] at hlog
  have h1 : Real.log j ≤ Real.log ((j : ℝ) * Real.log 4) :=
    Real.log_le_log hj' (by nlinarith)
  have h3 : Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e) ≤ Real.exp (-(2 * Real.log j)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine h3.trans (le_of_eq ?_)
  rw [Real.exp_neg, show (2 : ℝ) * Real.log j = Real.log ((j : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]
