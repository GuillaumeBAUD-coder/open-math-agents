import OMAReductions.R_PartitionParity_zheng_odd_R1

/-! Since c / 2 is below the liminf, eventually c / 2 < f(X) / sqrt X, that is
sqrt X ≤ (2 / c) f(X) for large positive X. -/

theorem OMA.solution : OMA.R_PartitionParity_zheng_odd_R1.H2 := by
  intro f c hc h
  have hlt : ((c / 2 : ℝ) : EReal) <
      Filter.liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) Filter.atTop :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) h
  have hev := Filter.eventually_lt_of_lt_liminf hlt
  refine Asymptotics.IsBigO.of_bound (2 / c) ?_
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with X hX hpos
  have hX' : c / 2 < f X / Real.sqrt X := EReal.coe_lt_coe_iff.1 hX
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.2 hpos
  rw [lt_div_iff₀ hs] at hX'
  rw [Real.norm_of_nonneg hs.le, div_mul_eq_mul_div, le_div_iff₀ hc]
  have hf : f X ≤ ‖f X‖ := le_abs_self _
  nlinarith
