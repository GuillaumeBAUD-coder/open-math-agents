import OMAReductions.R_Erdos17_erdos_17_variants_upper_BES_R1

-- Step Erdos17.erdos_17.variants.upper_BES.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos17_erdos_17_variants_upper_BES_R1.H2 := by
  intro A hA c hc
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_gt_atTop 1, hlog2.eventually_ge_atTop (A / c)] with x h1 h2
  have hlog_pos : 0 < Real.log (x : ℝ) := by linarith
  have hy_pos : 0 < Real.log (Real.log (x : ℝ)) := lt_of_lt_of_le (div_pos hA hc) h2
  have hlhs : 0 ≤ (x : ℝ) * Real.exp (-c * (Real.log (Real.log (x : ℝ))) ^ 2) :=
    mul_nonneg (Nat.cast_nonneg x) (Real.exp_pos _).le
  have hrhs : 0 ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A :=
    div_nonneg (Nat.cast_nonneg x) (Real.rpow_nonneg hlog_pos.le A)
  rw [Real.norm_of_nonneg hlhs, Real.norm_of_nonneg hrhs, one_mul, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
  rw [← Real.rpow_neg hlog_pos.le A, Real.rpow_def_of_pos hlog_pos]
  apply Real.exp_le_exp.mpr
  have hAy : A ≤ Real.log (Real.log (x : ℝ)) * c := (div_le_iff₀ hc).mp h2
  nlinarith
