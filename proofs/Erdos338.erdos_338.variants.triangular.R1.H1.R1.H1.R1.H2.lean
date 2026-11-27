import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1

/-! For N = 8 m + 3 beyond 3^20 the fourth root is small against the power 3/10: with
s the iterated integer square root, s^4 is at most N, so (3 s)^20 is at most
3^20 N^5, which is below N^6. -/

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2 := by
  filter_upwards [Filter.eventually_ge_atTop (3 ^ 20)] with m hm
  show (3 * (((8 * m + 3).sqrt.sqrt : ℕ) : ℝ)) < (((8 * m + 3 : ℕ) : ℝ)) ^ (3 / 10 : ℝ)
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * m + 3 := ⟨_, rfl⟩
  rw [← hN]
  have hNbig : 3 ^ 20 < N := by
    rw [hN]
    have h320 : (3:ℕ) ^ 20 = 3486784401 := by norm_num
    rw [h320] at hm ⊢
    omega
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hNbig
  obtain ⟨s, hs⟩ : ∃ s, s = N.sqrt.sqrt := ⟨_, rfl⟩
  rw [← hs]
  have h1 : s ^ 2 ≤ N.sqrt := by
    rw [hs]
    exact Nat.sqrt_le' N.sqrt
  have h2 : N.sqrt ^ 2 ≤ N := Nat.sqrt_le' N
  have hs4 : s ^ 4 ≤ N := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ N.sqrt ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ N := h2
  have hnat : (3 * s) ^ 20 < N ^ 6 := by
    calc (3 * s) ^ 20 = 3 ^ 20 * (s ^ 4) ^ 5 := by ring
      _ ≤ 3 ^ 20 * N ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs4 5)
      _ < N * N ^ 5 := Nat.mul_lt_mul_of_pos_right hNbig (Nat.pow_pos hNpos)
      _ = N ^ 6 := by ring
  have hreal : ((3:ℝ) * (s:ℝ)) ^ 20 < (N:ℝ) ^ 6 := by exact_mod_cast hnat
  refine lt_of_pow_lt_pow_left₀ 20 (by positivity) ?_
  rw [← Real.rpow_natCast ((N:ℝ) ^ (3 / 10 : ℝ)) 20, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have h6 : (3 / 10 : ℝ) * ((20:ℕ):ℝ) = ((6:ℕ):ℝ) := by norm_num
  rw [h6, Real.rpow_natCast]
  exact hreal
