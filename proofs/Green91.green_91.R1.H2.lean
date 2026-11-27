import OMAReductions.R_Green91_green_91_R1

/-! By the definition of little o with constant 1/100, eventually |f n| ≤ n / 100. -/

theorem OMA.solution : OMA.R_Green91_green_91_R1.H2 := by
  intro f hf
  filter_upwards [hf.def (by norm_num : (0 : ℝ) < 1 / 100)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)] at hn
  have h1 : f n ≤ ‖f n‖ := le_abs_self _
  linarith
