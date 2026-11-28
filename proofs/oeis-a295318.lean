import OMAStatements.S_oeis_a295318

theorem A295318_aux_even (n : ℤ) (M : ℕ) :
    (∑ i ∈ Finset.Icc 1 (2 * M), (i : ℤ) * (n - i) * (((i + 1) % 2 : ℕ) : ℤ)) * 3
      = M * (M + 1) * (3 * n - 4 * M - 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    rw [e, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      add_mul, add_mul, ih]
    have h1 : (2 * M + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * M + 1 + 1 + 1) % 2 = 1 := by omega
    rw [h1, h2]
    push_cast
    ring

theorem A295318_a_cast (n : ℕ) :
    (OMA.S_oeis_a295318.a n : ℤ) =
      ∑ i ∈ Finset.Icc 1 ((n - 1) / 2), (i : ℤ) * ((n : ℤ) - i) * (((i + 1) % 2 : ℕ) : ℤ) := by
  unfold OMA.S_oeis_a295318.a
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hin : i ≤ n := by omega
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hin]

theorem A295318_closed (k t : ℕ) (ht1 : 1 ≤ t) (ht4 : t ≤ 4) :
    (OMA.S_oeis_a295318.a (4 * k + t) : ℤ) * 3 = k * (k + 1) * (8 * k + 3 * t - 2) := by
  rw [A295318_a_cast]
  have hcases : (4 * k + t - 1) / 2 = 2 * k ∨ (4 * k + t - 1) / 2 = 2 * k + 1 := by omega
  rcases hcases with h | h
  · rw [h, A295318_aux_even]
    push_cast
    ring
  · rw [h, Finset.sum_Icc_succ_top (by omega), add_mul, A295318_aux_even]
    have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
    rw [h1]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a295318.main := by
  intro n hn
  have c : ∀ (j t : ℕ), 1 ≤ t → t ≤ 4 → ∀ N, N = 4 * j + t →
      (OMA.S_oeis_a295318.a N : ℤ) * 3 = j * (j + 1) * (8 * j + 3 * t - 2) := by
    intro j t h1 h4 N hN
    subst hN
    exact A295318_closed j t h1 h4
  obtain ⟨m, s, hs, hns⟩ : ∃ m s, s < 4 ∧ n = 4 * m + s + 14 :=
    ⟨(n - 14) / 4, (n - 14) % 4, by omega, by omega⟩
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hs' with rfl | rfl | rfl | rfl
  · have h0 := c (m + 3) 2 (by norm_num) (by norm_num) n (by omega)
    have h1 := c (m + 3) 1 (by norm_num) (by norm_num) (n - 1) (by omega)
    have h4 := c (m + 2) 2 (by norm_num) (by norm_num) (n - 4) (by omega)
    have h5 := c (m + 2) 1 (by norm_num) (by norm_num) (n - 5) (by omega)
    have h8 := c (m + 1) 2 (by norm_num) (by norm_num) (n - 8) (by omega)
    have h9 := c (m + 1) 1 (by norm_num) (by norm_num) (n - 9) (by omega)
    have h12 := c m 2 (by norm_num) (by norm_num) (n - 12) (by omega)
    have h13 := c m 1 (by norm_num) (by norm_num) (n - 13) (by omega)
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have h0 := c (m + 3) 3 (by norm_num) (by norm_num) n (by omega)
    have h1 := c (m + 3) 2 (by norm_num) (by norm_num) (n - 1) (by omega)
    have h4 := c (m + 2) 3 (by norm_num) (by norm_num) (n - 4) (by omega)
    have h5 := c (m + 2) 2 (by norm_num) (by norm_num) (n - 5) (by omega)
    have h8 := c (m + 1) 3 (by norm_num) (by norm_num) (n - 8) (by omega)
    have h9 := c (m + 1) 2 (by norm_num) (by norm_num) (n - 9) (by omega)
    have h12 := c m 3 (by norm_num) (by norm_num) (n - 12) (by omega)
    have h13 := c m 2 (by norm_num) (by norm_num) (n - 13) (by omega)
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have h0 := c (m + 3) 4 (by norm_num) (by norm_num) n (by omega)
    have h1 := c (m + 3) 3 (by norm_num) (by norm_num) (n - 1) (by omega)
    have h4 := c (m + 2) 4 (by norm_num) (by norm_num) (n - 4) (by omega)
    have h5 := c (m + 2) 3 (by norm_num) (by norm_num) (n - 5) (by omega)
    have h8 := c (m + 1) 4 (by norm_num) (by norm_num) (n - 8) (by omega)
    have h9 := c (m + 1) 3 (by norm_num) (by norm_num) (n - 9) (by omega)
    have h12 := c m 4 (by norm_num) (by norm_num) (n - 12) (by omega)
    have h13 := c m 3 (by norm_num) (by norm_num) (n - 13) (by omega)
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
  · have h0 := c (m + 4) 1 (by norm_num) (by norm_num) n (by omega)
    have h1 := c (m + 3) 4 (by norm_num) (by norm_num) (n - 1) (by omega)
    have h4 := c (m + 3) 1 (by norm_num) (by norm_num) (n - 4) (by omega)
    have h5 := c (m + 2) 4 (by norm_num) (by norm_num) (n - 5) (by omega)
    have h8 := c (m + 2) 1 (by norm_num) (by norm_num) (n - 8) (by omega)
    have h9 := c (m + 1) 4 (by norm_num) (by norm_num) (n - 9) (by omega)
    have h12 := c (m + 1) 1 (by norm_num) (by norm_num) (n - 12) (by omega)
    have h13 := c m 4 (by norm_num) (by norm_num) (n - 13) (by omega)
    push_cast at h0 h1 h4 h5 h8 h9 h12 h13
    linarith
