import OMAReductions.R_PartitionParity_bellaiche_nicolas_even_R1

/-! For X with log log X ≥ 0 the function sqrt X log log X is nonnegative, so its norm is at
most (1 / c) F(X) ≤ (1 / c) |F(X)|. -/

theorem OMA.solution : OMA.R_PartitionParity_bellaiche_nicolas_even_R1.H2 := by
  intro c F hc h
  have t2 : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine Asymptotics.IsBigO.of_bound (1 / c) ?_
  filter_upwards [t2.eventually_ge_atTop 0, Filter.eventually_gt_atTop (1 : ℝ)] with X h2 hX
  have h0 : 0 ≤ Real.sqrt X * Real.log (Real.log X) := mul_nonneg (Real.sqrt_nonneg X) h2
  have hF := h X hX
  have hFn : F X ≤ ‖F X‖ := le_abs_self _
  rw [Real.norm_of_nonneg h0, div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  nlinarith
