import OMAReductions.R_LatinSquare_growthRateZn_R1
import Mathlib

open Filter Real Stirling
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_growthRateZn_R1.H2 := by
  obtain ⟨a,ha,hs⟩ := stirlingSeq_has_pos_limit_a
  have nr : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have sm := (hs.log ha.ne').div_atTop nr
  have lg : Tendsto (fun n : ℕ ↦ log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp nr
  have cn := (tendsto_const_nhds (x := Real.log 2 / 2)).div_atTop nr
  have lim := ((sm.add cn).add (lg.const_mul (3/2 : ℝ))).sub (tendsto_const_nhds (x := (1:ℝ)))
  norm_num at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [log_stirlingSeq_formula, log_mul (by norm_num) hn'.ne',
    log_div hn'.ne' (exp_pos _).ne', log_exp]
  field_simp
  ring
