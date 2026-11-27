import OMAReductions.R_Erdos830_erdos_830_variants_pomerance_R1

/-! Write L = log x. Eventually |o(x)| ≤ 1/4, L ≥ 4096 and log log L ≥ 1. Then
sqrt (L log log L) ≥ sqrt L = L^(1/3) L^(1/6) ≥ 4 L^(1/3), so
(1/2 + o(x)) sqrt (L log log L) ≥ L^(1/3), and the third root of the positive number L is
L^(1/3). -/

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_pomerance_R1.H2 := by
  intro o ho
  have t1 : Filter.Tendsto (fun x : ℝ => Real.log x) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop
  have t3 : Filter.Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp t1)
  have ho' := ho.def (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [ho', t1.eventually_ge_atTop 4096, t3.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hox hL h3 hx
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log x := ⟨_, rfl⟩
  rw [← hLdef] at hL h3 ⊢
  have hLpos : 0 < L := by linarith
  have hox' : -(1 / 4 : ℝ) ≤ o x := by
    have h := (abs_le.1 (by simpa using hox : |o x| ≤ 1 / 4)).1
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = L ^ ((3 : ℝ)⁻¹) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = L ^ ((6 : ℝ)⁻¹) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ Real.rpow_nonneg hLpos.le _
  have hb0 : 0 ≤ b := hb ▸ Real.rpow_nonneg hLpos.le _
  have hroot : Real.nthRoot 3 L = a := by
    rw [Real.nthRoot_of_odd (by decide), abs_of_pos hLpos, sign_pos hLpos, ha]
    norm_num
  have hsqrt : Real.sqrt L = a * b := by
    rw [Real.sqrt_eq_rpow, ha, hb, ← Real.rpow_add hLpos]
    norm_num
  have hb6 : b ^ 6 = L := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hb4 : 4 ≤ b := by
    by_contra hlt
    have h := pow_lt_pow_left₀ (not_le.1 hlt) hb0 (by norm_num : (6 : ℕ) ≠ 0)
    rw [hb6] at h
    norm_num at h
    linarith
  have hS : Real.sqrt L ≤ Real.sqrt (L * Real.log (Real.log L)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hkey : a ≤ (1 / 2 + o x) * Real.sqrt (L * Real.log (Real.log L)) := by
    have h1 : 4 * a ≤ Real.sqrt (L * Real.log (Real.log L)) := by
      rw [hsqrt] at hS
      nlinarith
    have h2 : (1 / 4 : ℝ) ≤ 1 / 2 + o x := by linarith
    nlinarith [Real.sqrt_nonneg (L * Real.log (Real.log L))]
  rw [hroot]
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.exp_le_exp.2
  linarith
