import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1

/-! Since log n ≤ 2 sqrt n, one has c n / log n ≥ c sqrt n / 2, which tends to infinity. -/

theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2 := by
  intro c hc d
  have t0 : Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have t1 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [t0.eventually_ge_atTop (2 * (d : ℝ) / c), t1.eventually_ge_atTop 1]
    with n hs hl
  have hlpos : 0 < Real.log (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    calc Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) / (1 / 2) := h
      _ = 2 * Real.sqrt (n : ℝ) := by ring
  have hd : 2 * (d : ℝ) ≤ c * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ hc] at hs
    linarith
  rw [le_div_iff₀ hlpos]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h1 := mul_le_mul_of_nonneg_left hlog hd0
  have h2 := mul_le_mul_of_nonneg_right hd hs0
  have h3 : c * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = c * (n : ℝ) := by rw [mul_assoc, hsq]
  linarith
