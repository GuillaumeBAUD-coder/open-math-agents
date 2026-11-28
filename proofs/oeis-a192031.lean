import OMAStatements.S_oeis_a192031

open PowerSeries OMA.S_oeis_a192031

lemma OMA.key (q j : ℕ) (hj : j < 4) : a (6 + 4 * q + j) = row (4 + (q : ℚ)) j := by
  unfold a
  rw [if_neg (show ¬ (6 + 4 * q + j < 3) by omega), if_neg (show ¬ (6 + 4 * q + j < 6) by omega),
    show (6 + 4 * q + j - 6) / 4 = q by omega, show (6 + 4 * q + j - 6) % 4 = j by omega]

lemma OMA.hrec : ∀ n : ℕ, 16 < n →
    a n = a (n-1) - a (n-2) + a (n-3) + 2*a (n-4) - 2*a (n-5) +
      2*a (n-6) - 2*a (n-7) - a (n-8) + a (n-9) - a (n-10) + a (n-11) := by
  intro n hn
  have k0 := fun q : ℕ => OMA.key q 0 (by norm_num)
  have k1 := fun q : ℕ => OMA.key q 1 (by norm_num)
  have k2 := fun q : ℕ => OMA.key q 2 (by norm_num)
  have k3 := fun q : ℕ => OMA.key q 3 (by norm_num)
  obtain ⟨t, rfl | rfl | rfl | rfl⟩ : ∃ t, n = 4 * t + 17 ∨ n = 4 * t + 18 ∨ n = 4 * t + 19 ∨
      n = 4 * t + 20 := ⟨(n - 17) / 4, by omega⟩
  · rw [show 4 * t + 17 - 11 = 6 + 4 * (t + 0) + 0 by omega,
      show 4 * t + 17 - 10 = 6 + 4 * (t + 0) + 1 by omega,
      show 4 * t + 17 - 9 = 6 + 4 * (t + 0) + 2 by omega,
      show 4 * t + 17 - 8 = 6 + 4 * (t + 0) + 3 by omega,
      show 4 * t + 17 - 7 = 6 + 4 * (t + 1) + 0 by omega,
      show 4 * t + 17 - 6 = 6 + 4 * (t + 1) + 1 by omega,
      show 4 * t + 17 - 5 = 6 + 4 * (t + 1) + 2 by omega,
      show 4 * t + 17 - 4 = 6 + 4 * (t + 1) + 3 by omega,
      show 4 * t + 17 - 3 = 6 + 4 * (t + 2) + 0 by omega,
      show 4 * t + 17 - 2 = 6 + 4 * (t + 2) + 1 by omega,
      show 4 * t + 17 - 1 = 6 + 4 * (t + 2) + 2 by omega,
      show 4 * t + 17 = 6 + 4 * (t + 2) + 3 by omega]
    simp only [k0, k1, k2, k3, row]
    push_cast
    ring
  · rw [show 4 * t + 18 - 11 = 6 + 4 * (t + 0) + 1 by omega,
      show 4 * t + 18 - 10 = 6 + 4 * (t + 0) + 2 by omega,
      show 4 * t + 18 - 9 = 6 + 4 * (t + 0) + 3 by omega,
      show 4 * t + 18 - 8 = 6 + 4 * (t + 1) + 0 by omega,
      show 4 * t + 18 - 7 = 6 + 4 * (t + 1) + 1 by omega,
      show 4 * t + 18 - 6 = 6 + 4 * (t + 1) + 2 by omega,
      show 4 * t + 18 - 5 = 6 + 4 * (t + 1) + 3 by omega,
      show 4 * t + 18 - 4 = 6 + 4 * (t + 2) + 0 by omega,
      show 4 * t + 18 - 3 = 6 + 4 * (t + 2) + 1 by omega,
      show 4 * t + 18 - 2 = 6 + 4 * (t + 2) + 2 by omega,
      show 4 * t + 18 - 1 = 6 + 4 * (t + 2) + 3 by omega,
      show 4 * t + 18 = 6 + 4 * (t + 3) + 0 by omega]
    simp only [k0, k1, k2, k3, row]
    push_cast
    ring
  · rw [show 4 * t + 19 - 11 = 6 + 4 * (t + 0) + 2 by omega,
      show 4 * t + 19 - 10 = 6 + 4 * (t + 0) + 3 by omega,
      show 4 * t + 19 - 9 = 6 + 4 * (t + 1) + 0 by omega,
      show 4 * t + 19 - 8 = 6 + 4 * (t + 1) + 1 by omega,
      show 4 * t + 19 - 7 = 6 + 4 * (t + 1) + 2 by omega,
      show 4 * t + 19 - 6 = 6 + 4 * (t + 1) + 3 by omega,
      show 4 * t + 19 - 5 = 6 + 4 * (t + 2) + 0 by omega,
      show 4 * t + 19 - 4 = 6 + 4 * (t + 2) + 1 by omega,
      show 4 * t + 19 - 3 = 6 + 4 * (t + 2) + 2 by omega,
      show 4 * t + 19 - 2 = 6 + 4 * (t + 2) + 3 by omega,
      show 4 * t + 19 - 1 = 6 + 4 * (t + 3) + 0 by omega,
      show 4 * t + 19 = 6 + 4 * (t + 3) + 1 by omega]
    simp only [k0, k1, k2, k3, row]
    push_cast
    ring
  · rw [show 4 * t + 20 - 11 = 6 + 4 * (t + 0) + 3 by omega,
      show 4 * t + 20 - 10 = 6 + 4 * (t + 1) + 0 by omega,
      show 4 * t + 20 - 9 = 6 + 4 * (t + 1) + 1 by omega,
      show 4 * t + 20 - 8 = 6 + 4 * (t + 1) + 2 by omega,
      show 4 * t + 20 - 7 = 6 + 4 * (t + 1) + 3 by omega,
      show 4 * t + 20 - 6 = 6 + 4 * (t + 2) + 0 by omega,
      show 4 * t + 20 - 5 = 6 + 4 * (t + 2) + 1 by omega,
      show 4 * t + 20 - 4 = 6 + 4 * (t + 2) + 2 by omega,
      show 4 * t + 20 - 3 = 6 + 4 * (t + 2) + 3 by omega,
      show 4 * t + 20 - 2 = 6 + 4 * (t + 3) + 0 by omega,
      show 4 * t + 20 - 1 = 6 + 4 * (t + 3) + 1 by omega,
      show 4 * t + 20 = 6 + 4 * (t + 3) + 2 by omega]
    simp only [k0, k1, k2, k3, row]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192031.main := by
  refine ⟨?_, OMA.hrec⟩
  ext k
  rw [show ((1-X)^3 * (1+X)^2 * (1+X^2)^3 : PowerSeries ℚ) =
      1 - X ^ 1 + X ^ 2 - X ^ 3 - 2 • X ^ 4 + 2 • X ^ 5 - 2 • X ^ 6 + 2 • X ^ 7 + X ^ 8 - X ^ 9 +
        X ^ 10 - X ^ 11 by ring,
    show (X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) : PowerSeries ℚ) =
      9 • X ^ 3 + 3 • X ^ 5 + 9 • X ^ 6 - 22 • X ^ 7 + 3 • X ^ 8 - 10 • X ^ 9 - 11 • X ^ 10 +
        16 • X ^ 11 + 2 • X ^ 12 + 6 • X ^ 13 + 3 • X ^ 14 - 3 • X ^ 15 - 3 • X ^ 16 by ring]
  simp only [mul_add, mul_sub, mul_one, mul_smul_comm, map_add, map_sub, map_nsmul,
    coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  by_cases hk : k < 17
  · interval_cases k <;> norm_num [a, row]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
    have h := OMA.hrec (m + 17) (by omega)
    simp only [show m + 17 - 1 = m + 16 from rfl, show m + 17 - 2 = m + 15 from rfl,
      show m + 17 - 3 = m + 14 from rfl, show m + 17 - 4 = m + 13 from rfl,
      show m + 17 - 5 = m + 12 from rfl, show m + 17 - 6 = m + 11 from rfl,
      show m + 17 - 7 = m + 10 from rfl, show m + 17 - 8 = m + 9 from rfl,
      show m + 17 - 9 = m + 8 from rfl, show m + 17 - 10 = m + 7 from rfl,
      show m + 17 - 11 = m + 6 from rfl] at h ⊢
    simp only [if_pos (show 1 ≤ m + 17 by omega),
      if_pos (show 2 ≤ m + 17 by omega),
      if_pos (show 3 ≤ m + 17 by omega),
      if_pos (show 4 ≤ m + 17 by omega),
      if_pos (show 5 ≤ m + 17 by omega),
      if_pos (show 6 ≤ m + 17 by omega),
      if_pos (show 7 ≤ m + 17 by omega),
      if_pos (show 8 ≤ m + 17 by omega),
      if_pos (show 9 ≤ m + 17 by omega),
      if_pos (show 10 ≤ m + 17 by omega),
      if_pos (show 11 ≤ m + 17 by omega),
      if_neg (show ¬ (m + 17 = 3) by omega),
      if_neg (show ¬ (m + 17 = 5) by omega),
      if_neg (show ¬ (m + 17 = 6) by omega),
      if_neg (show ¬ (m + 17 = 7) by omega),
      if_neg (show ¬ (m + 17 = 8) by omega),
      if_neg (show ¬ (m + 17 = 9) by omega),
      if_neg (show ¬ (m + 17 = 10) by omega),
      if_neg (show ¬ (m + 17 = 11) by omega),
      if_neg (show ¬ (m + 17 = 12) by omega),
      if_neg (show ¬ (m + 17 = 13) by omega),
      if_neg (show ¬ (m + 17 = 14) by omega),
      if_neg (show ¬ (m + 17 = 15) by omega),
      if_neg (show ¬ (m + 17 = 16) by omega),
      nsmul_eq_mul]
    push_cast
    linarith
