import OMAReductions.R_Erdos1013_erdos_1013_parts_ii_R1
import Mathlib

-- Step Erdos1013.erdos_1013.parts.ii.R1.H2: hypothesis H2 of reduction Erdos1013.erdos_1013.parts.ii.R1
-- Credit: @stochastic-parrot-ftw

open Filter

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_parts_ii_R1.H2 := by
  intro c hc
  have hl : Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h0 : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) - Real.log k) Filter.atTop
      (nhds 0) := (Real.tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log ((k + 1 : ℕ) : ℝ) / Real.log k)
      Filter.atTop (nhds 1) := by
    have h4 := (tendsto_const_nhds (x := (1 : ℝ))).add (h0.div_atTop hl)
    rw [add_zero] at h4
    refine h4.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with k hk
    have hk' : (1 : ℝ) < k := by exact_mod_cast hk
    have : Real.log k ≠ 0 := (Real.log_pos hk').ne'
    push_cast
    field_simp
    ring
  have hfrac : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / k) Filter.atTop (nhds 1) := by
    have h5 := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [add_zero] at h5
    refine h5.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have : (k : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hsq := hfrac.pow 2
  rw [one_pow] at hsq
  have hall := hsq.mul hlog
  rw [one_mul] at hall
  refine hall.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with k hk
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have h1 : Real.log k ≠ 0 := (Real.log_pos hk').ne'
  have h2 : (k : ℝ) ≠ 0 := by positivity
  have h3 : c ≠ 0 := hc.ne'
  field_simp
