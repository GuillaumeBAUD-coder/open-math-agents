import OMAReductions.R_Green14_green_14_polynomial_k_eq_3_R1

/-! With L = log r, eventually the exponent 4/3 - o(r) is at least 5/4 and L^(1/4) exceeds
M = (d + 1 + |log K|) / c, so c L^(5/4) is at least (d + 1 + |log K|) L, which is more than
log K + d L. Hence exp (c L^(4/3 - o(r))) is not at most K r^d. -/

theorem OMA.solution : OMA.R_Green14_green_14_polynomial_k_eq_3_R1.H2 := by
  intro c hc o ho d hbig
  obtain ⟨K, hKpos, hK⟩ := hbig.exists_pos
  have hK' := hK.bound
  have ho' : ∀ᶠ r in Filter.atTop, o r ≤ 1 / 12 :=
    ho.eventually (eventually_le_nhds (by norm_num))
  have tlog : Filter.Tendsto (fun r : ℕ => Real.log (r:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ((d:ℝ) + 1 + |Real.log K|) / c := ⟨_, rfl⟩
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  obtain ⟨r, hr1, hr2, hr3⟩ :=
    (hK'.and (ho'.and (tlog.eventually_ge_atTop (max 1 (M ^ 4))))).exists
  beta_reduce at hr1 hr3
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (r:ℝ) := ⟨_, rfl⟩
  rw [← hL] at hr1 hr3
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hr3
  have hLM : M ^ 4 ≤ L := le_trans (le_max_right _ _) hr3
  have hLpos : 0 < L := by linarith
  have hrpos : (0:ℝ) < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hL
      simp at hL
      linarith
    · exact_mod_cast h
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (by positivity)] at hr1
  have hrd : (r:ℝ) ^ d = Real.exp (d * L) := by
    rw [Real.exp_nat_mul, hL, Real.exp_log hrpos]
  have hKexp : K = Real.exp (Real.log K) := (Real.exp_log hKpos).symm
  rw [hrd] at hr1
  have hr1' : Real.exp (c * L ^ (4 / 3 - o r)) ≤ Real.exp (Real.log K + d * L) := by
    rw [Real.exp_add, ← hKexp]
    exact hr1
  rw [Real.exp_le_exp] at hr1'
  have h54 : L ^ ((5:ℝ) / 4) ≤ L ^ (4 / 3 - o r) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hquarter : M ≤ L ^ ((1:ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by positivity) hLM (by norm_num : (0:ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hMpos.le,
      show ((4:ℕ):ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one] at h
  have hsplit : L ^ ((5:ℝ) / 4) = L * L ^ ((1:ℝ) / 4) := by
    rw [show (5:ℝ) / 4 = 1 + 1 / 4 by norm_num, Real.rpow_add hLpos, Real.rpow_one]
  have h1 : c * (L * M) ≤ c * L ^ (4 / 3 - o r) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    calc L * M ≤ L * L ^ ((1:ℝ) / 4) := mul_le_mul_of_nonneg_left hquarter hLpos.le
      _ = L ^ ((5:ℝ) / 4) := hsplit.symm
      _ ≤ _ := h54
  have h2 : c * (L * M) = ((d:ℝ) + 1 + |Real.log K|) * L := by
    rw [hM]
    field_simp
  have h3 := le_abs_self (Real.log K)
  have h4 := abs_nonneg (Real.log K)
  have h5 := mul_le_mul_of_nonneg_right hL1 (by linarith : (0:ℝ) ≤ 1 + |Real.log K|)
  nlinarith
