import OMAReductions.R_Erdos686_erdos_686_R1

-- Credit: @jagong-cmu

theorem h1 :
  ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
    (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  intro N hN hns
  have hnsZ : ¬ IsSquare (N : ℤ) := by
    rwa [Int.isSquare_natCast_iff]
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (d := (N : ℤ)) (by omega) hnsZ
  set a := x.natAbs with ha_def
  set b := y.natAbs with hb_def
  have hb : 1 ≤ b := by
    have := Int.natAbs_pos.mpr hy
    omega
  have hab : a ^ 2 = 1 + N * b ^ 2 := by
    have h1 : ((a : ℤ)) ^ 2 = x ^ 2 := Int.natAbs_sq x
    have h2 : ((b : ℤ)) ^ 2 = y ^ 2 := Int.natAbs_sq y
    have : ((a ^ 2 : ℕ) : ℤ) = ((1 + N * b ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [h1, h2]
      linarith
    exact_mod_cast this
  have ha2 : 2 ≤ a := by
    by_contra hc
    push Not at hc
    have : a ^ 2 ≤ 1 := by
      interval_cases a <;> simp
    have : N * b ^ 2 ≥ 2 := by
      have : b ^ 2 ≥ 1 := Nat.one_le_pow _ _ hb
      nlinarith
    omega
  have hs : 2 ≤ N * b ^ 2 := by
    have : b ^ 2 ≥ 1 := Nat.one_le_pow _ _ hb
    nlinarith
  have habp : 2 ≤ a * b := by nlinarith
  refine ⟨2, le_refl _, N * b ^ 2 + a * b - 1, N * b ^ 2 + N * a * b - 1, ?_, ?_⟩
  · have : N * a * b ≥ a * b + a * b := by
      have : N * (a * b) ≥ 2 * (a * b) := Nat.mul_le_mul_right _ hN
      nlinarith
    omega
  · have hn : N * b ^ 2 + a * b - 1 + 1 = N * b ^ 2 + a * b := by omega
    have hm : N * b ^ 2 + N * a * b - 1 + 1 = N * b ^ 2 + N * a * b := by
      have : N * a * b ≥ 1 := by nlinarith
      omega
    simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self,
      Finset.prod_singleton]
    have hden : ((N * b ^ 2 + a * b - 1 + 1 : ℕ) : ℚ) * ((N * b ^ 2 + a * b - 1 + 2 : ℕ) : ℚ) ≠ 0 := by
      positivity
    push_cast at hden ⊢
    rw [eq_div_iff hden]
    have hnq : ((N * b ^ 2 + a * b - 1 : ℕ) : ℚ) + 1 = (N : ℚ) * b ^ 2 + a * b := by
      exact_mod_cast hn
    have hmq : ((N * b ^ 2 + N * a * b - 1 : ℕ) : ℚ) + 1 = (N : ℚ) * b ^ 2 + N * a * b := by
      exact_mod_cast hm
    have habq : (a : ℚ) ^ 2 = 1 + N * b ^ 2 := by exact_mod_cast hab
    have e1 : ((N * b ^ 2 + a * b - 1 : ℕ) : ℚ) + 2 = (N : ℚ) * b ^ 2 + a * b + 1 := by
      linarith
    have e2 : ((N * b ^ 2 + N * a * b - 1 : ℕ) : ℚ) + 2 = (N : ℚ) * b ^ 2 + N * a * b + 1 := by
      linarith
    rw [hnq, hmq, e1, e2]
    linear_combination (-(N : ℚ) * ((N : ℚ) - 1) * (b : ℚ) ^ 2) * habq

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := h1
