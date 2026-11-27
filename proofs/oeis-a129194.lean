import OMAStatements.S_oeis_a129194

theorem OMA.solution : type_of% @OMA.S_oeis_a129194.main := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 0 < m := by omega
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq : (4 : ℚ) / ((2 * m : ℕ) : ℚ) - 2 / ((2 * m : ℕ) : ℚ) ^ 2 =
        ((4 * (m : ℤ) - 1 : ℤ) : ℚ) / ((2 * (m : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
      ring
    have hcop : IsCoprime (4 * (m : ℤ) - 1) (2 * (m : ℤ) ^ 2) := by
      apply IsCoprime.mul_right
      · exact ⟨-1, 2 * m, by ring⟩
      · apply IsCoprime.pow_right
        exact ⟨-1, 4, by ring⟩
    have hden := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < 2 * (m : ℤ) ^ 2)
      (Int.isCoprime_iff_gcd_eq_one.1 hcop)
    rw [hq]
    have h3 : ((((4 * (m : ℤ) - 1 : ℤ) : ℚ) / ((2 * (m : ℤ) ^ 2 : ℤ) : ℚ)).den : ℚ) =
        2 * (m : ℚ) ^ 2 := by
      exact_mod_cast hden
    rw [h3]
    unfold OMA.S_oeis_a129194.a
    rw [pow_mul]
    push_cast
    norm_num
    ring
  · have hq : (4 : ℚ) / ((2 * m + 1 : ℕ) : ℚ) - 2 / ((2 * m + 1 : ℕ) : ℚ) ^ 2 =
        ((4 * (2 * (m : ℤ) + 1) - 2 : ℤ) : ℚ) / (((2 * (m : ℤ) + 1) ^ 2 : ℤ) : ℚ) := by
      have hm' : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    have hcop : IsCoprime (4 * (2 * (m : ℤ) + 1) - 2) ((2 * (m : ℤ) + 1) ^ 2) := by
      apply IsCoprime.pow_right
      exact ⟨m, -(4 * m - 1), by ring⟩
    have hden := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < (2 * (m : ℤ) + 1) ^ 2)
      (Int.isCoprime_iff_gcd_eq_one.1 hcop)
    rw [hq]
    have h3 : ((((4 * (2 * (m : ℤ) + 1) - 2 : ℤ) : ℚ) / (((2 * (m : ℤ) + 1) ^ 2 : ℤ) : ℚ)).den : ℚ) =
        (2 * (m : ℚ) + 1) ^ 2 := by
      exact_mod_cast hden
    rw [h3]
    unfold OMA.S_oeis_a129194.a
    rw [pow_succ, pow_mul]
    push_cast
    norm_num
    ring
