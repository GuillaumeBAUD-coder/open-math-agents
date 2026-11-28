import OMAStatements.S_oeis_a187035

open PowerSeries OMA.S_oeis_a187035

private theorem a_closed (n : ℕ) :
    a n = ((n / 2 + 1 - (n + 2) / 3 : ℕ) : ℤ) * (-1) ^ n := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      T (n - k) k = if k ∈ Finset.Ico ((n + 2) / 3) (n / 2 + 1) then (-1 : ℤ) ^ n else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold T
    have hiff : (k ≤ n - k ∧ 0 < Nat.choose k (n - k - k)) ↔
        k ∈ Finset.Ico ((n + 2) / 3) (n / 2 + 1) := by
      have hch : 0 < Nat.choose k (n - k - k) ↔ n - k - k ≤ k := by
        constructor
        · intro h
          by_contra hlt
          rw [Nat.choose_eq_zero_of_lt (by omega)] at h
          exact lt_irrefl 0 h
        · exact Nat.choose_pos
      rw [hch, Finset.mem_Ico]
      omega
    by_cases h : k ∈ Finset.Ico ((n + 2) / 3) (n / 2 + 1)
    · rw [if_pos (hiff.mpr h), if_pos h]
      rw [Finset.mem_Ico] at h
      have hn : n = (n - k - k) + 2 * k := by omega
      conv_rhs => rw [hn]
      rw [pow_add, pow_mul]
      simp
    · rw [if_neg (mt hiff.mp h), if_neg h]
  have hsub : Finset.Ico ((n + 2) / 3) (n / 2 + 1) ⊆ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  unfold a
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

private theorem a_rec (m : ℕ) : a (m + 5) = a (m + 3) - a (m + 2) + a m := by
  have hcount : (((m + 5) / 2 + 1 - (m + 5 + 2) / 3 : ℕ) : ℤ) =
      (((m + 3) / 2 + 1 - (m + 3 + 2) / 3 : ℕ) : ℤ) +
      (((m + 2) / 2 + 1 - (m + 2 + 2) / 3 : ℕ) : ℤ) -
      ((m / 2 + 1 - (m + 2) / 3 : ℕ) : ℤ) := by
    omega
  rw [a_closed, a_closed, a_closed, a_closed, hcount]
  simp only [pow_add]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a187035.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
      show m + 5 - 5 = m by omega]
    exact a_rec m
  · have hP : ((1 - X) * (1 - X + X ^ 2) * (1 + X) ^ 2 : ℤ⟦X⟧) =
        1 - X ^ 2 + X ^ 3 - X ^ 5 := by ring
    rw [hP, mul_comm]
    simp only [sub_mul, add_mul, one_mul]
    ext n
    simp only [map_add, map_sub, coeff_X_pow_mul', coeff_mk, coeff_one]
    match n with
    | 0 => simp [a_closed]
    | 1 => simp [a_closed]
    | 2 => simp [a_closed]
    | 3 => simp [a_closed]
    | 4 => simp [a_closed]
    | m + 5 =>
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega,
        show m + 5 - 5 = m by omega, a_rec]
      ring
