import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1

/-! With y = log log log m and L2 = log log m = exp y, the bound exp y ≥ y^4 / 24 gives
L2 log y / (9 y^3) ≥ y / 216 once log y ≥ 1, which exceeds c for y ≥ 216 c. -/

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H3 := by
  intro c hc
  have t1 : Filter.Tendsto (fun m : ℕ => Real.log (m:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have t3 : Filter.Tendsto (fun m : ℕ => Real.log (Real.log (Real.log (m:ℝ))))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp t1)
  filter_upwards [t1.eventually_ge_atTop 3, t3.eventually_ge_atTop (max 3 (216 * c))]
    with m h1 h3
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (m:ℝ) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2, L2 = Real.log L := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = Real.log L2 := ⟨_, rfl⟩
  rw [← hL] at h1 h3 ⊢
  rw [← hL2] at h3 ⊢
  rw [← hy] at h3 ⊢
  have hy3 : 3 ≤ y := le_trans (le_max_left _ _) h3
  have hyc : 216 * c ≤ y := le_trans (le_max_right _ _) h3
  have hL2pos : 0 < L2 := by
    rw [hL2]
    exact Real.log_pos (by linarith)
  have hexp : Real.exp y = L2 := by rw [hy, Real.exp_log hL2pos]
  have hpow : y ^ 4 / 24 ≤ L2 := by
    rw [← hexp]
    have h := Real.pow_div_factorial_le_exp y (by linarith) 4
    have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rwa [h24] at h
  have hlogy : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    linarith
  have hy3pos : (0:ℝ) < y ^ 3 := pow_pos (by linarith) 3
  have h6 := mul_le_mul_of_nonneg_right hyc hy3pos.le
  have h7 : L2 ≤ L2 * Real.log y := le_mul_of_one_le_right hL2pos.le hlogy
  have h5 : 9 * y ^ 3 * c ≤ L2 * Real.log y := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have h8 := mul_le_mul_of_nonneg_left h5 hL0
  rw [le_div_iff₀ (by positivity)]
  linarith
