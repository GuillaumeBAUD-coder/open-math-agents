import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1

open Filter in
theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2 := by
  intro c hc d
  filter_upwards [(Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds (div_pos hc (by positivity : (0 : ℝ) < d + 1))),
    eventually_ge_atTop 2] with n h hn
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have := (div_lt_div_iff₀ (by linarith : (0 : ℝ) < n) (by positivity)).mp h
  have hl := Real.log_pos (by linarith : (1 : ℝ) < n)
  rw [le_div_iff₀ hl]
  linarith
