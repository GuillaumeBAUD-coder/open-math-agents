import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1

/-! For x ≥ 1 a real power of x is nondecreasing in the exponent, and 2/7 < 0.33336704. -/

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_lower_bound_R1.H2 := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
