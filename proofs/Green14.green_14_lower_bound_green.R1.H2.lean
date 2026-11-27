import OMAReductions.R_Green14_green_14_lower_bound_green_R1

/-! Once log r ≥ 1, the power (log r)^(4/3 - o(r)) is at most (log r)^(2 - o(r)), so the
first exponential is at most the second. -/

theorem OMA.solution : OMA.R_Green14_green_14_lower_bound_green_R1.H2 := by
  intro c hc o
  have tlog : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [tlog.eventually_ge_atTop 1] with r hr
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hr (by linarith)) hc.le
