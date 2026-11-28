import OMAStatements.S_oeis_a057870

open PowerSeries OMA.S_oeis_a057870

lemma OMA.k0 (q : ℕ) : a (6 * q + 0) = (5*((6 * q + 0 : ℕ) : ℚ)^3 - 13*((6 * q + 0 : ℕ) : ℚ)^2 + 12*((6 * q + 0 : ℕ) : ℚ)) / 12 := by
  simp only [a, show (6 * q + 0) % 6 = 0 by omega]

lemma OMA.k1 (q : ℕ) : a (6 * q + 1) = (5*((6 * q + 1 : ℕ) : ℚ)^3 - 14*((6 * q + 1 : ℕ) : ℚ)^2 + 13*((6 * q + 1 : ℕ) : ℚ) - 4) / 12 := by
  simp only [a, show (6 * q + 1) % 6 = 1 by omega]

lemma OMA.k2 (q : ℕ) : a (6 * q + 2) = (5*((6 * q + 2 : ℕ) : ℚ)^3 - 13*((6 * q + 2 : ℕ) : ℚ)^2 + 16*((6 * q + 2 : ℕ) : ℚ) - 8) / 12 := by
  simp only [a, show (6 * q + 2) % 6 = 2 by omega]

lemma OMA.k3 (q : ℕ) : a (6 * q + 3) = (5*((6 * q + 3 : ℕ) : ℚ)^3 - 14*((6 * q + 3 : ℕ) : ℚ)^2 + 9*((6 * q + 3 : ℕ) : ℚ)) / 12 := by
  simp only [a, show (6 * q + 3) % 6 = 3 by omega]

lemma OMA.k4 (q : ℕ) : a (6 * q + 4) = (5*((6 * q + 4 : ℕ) : ℚ)^3 - 13*((6 * q + 4 : ℕ) : ℚ)^2 + 16*((6 * q + 4 : ℕ) : ℚ) - 8) / 12 := by
  simp only [a, show (6 * q + 4) % 6 = 4 by omega]

lemma OMA.k5 (q : ℕ) : a (6 * q + 5) = (5*((6 * q + 5 : ℕ) : ℚ)^3 - 14*((6 * q + 5 : ℕ) : ℚ)^2 + 13*((6 * q + 5 : ℕ) : ℚ) - 4) / 12 := by
  simp only [a, show (6 * q + 5) % 6 = 5 by omega]

lemma OMA.hrec : ∀ n : ℕ, 13 < n →
    a n = 2*a (n-2) + a (n-3) - a (n-4) - 2*a (n-5) + a (n-6) +
      a (n-7) - 2*a (n-8) - a (n-9) + a (n-10) + 2*a (n-11) - a (n-13) := by
  intro n hn
  obtain ⟨t, rfl | rfl | rfl | rfl | rfl | rfl⟩ : ∃ t, n = 6 * t + 14 ∨ n = 6 * t + 15 ∨ n = 6 * t + 16 ∨
      n = 6 * t + 17 ∨ n = 6 * t + 18 ∨ n = 6 * t + 19 := ⟨(n - 14) / 6, by omega⟩
  · rw [show 6 * t + 14 - 13 = 6 * (t + 0) + 1 by omega,
      show 6 * t + 14 - 11 = 6 * (t + 0) + 3 by omega,
      show 6 * t + 14 - 10 = 6 * (t + 0) + 4 by omega,
      show 6 * t + 14 - 9 = 6 * (t + 0) + 5 by omega,
      show 6 * t + 14 - 8 = 6 * (t + 1) + 0 by omega,
      show 6 * t + 14 - 7 = 6 * (t + 1) + 1 by omega,
      show 6 * t + 14 - 6 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 14 - 5 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 14 - 4 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 14 - 3 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 14 - 2 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 14 = 6 * (t + 2) + 2 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring
  · rw [show 6 * t + 15 - 13 = 6 * (t + 0) + 2 by omega,
      show 6 * t + 15 - 11 = 6 * (t + 0) + 4 by omega,
      show 6 * t + 15 - 10 = 6 * (t + 0) + 5 by omega,
      show 6 * t + 15 - 9 = 6 * (t + 1) + 0 by omega,
      show 6 * t + 15 - 8 = 6 * (t + 1) + 1 by omega,
      show 6 * t + 15 - 7 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 15 - 6 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 15 - 5 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 15 - 4 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 15 - 3 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 15 - 2 = 6 * (t + 2) + 1 by omega,
      show 6 * t + 15 = 6 * (t + 2) + 3 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring
  · rw [show 6 * t + 16 - 13 = 6 * (t + 0) + 3 by omega,
      show 6 * t + 16 - 11 = 6 * (t + 0) + 5 by omega,
      show 6 * t + 16 - 10 = 6 * (t + 1) + 0 by omega,
      show 6 * t + 16 - 9 = 6 * (t + 1) + 1 by omega,
      show 6 * t + 16 - 8 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 16 - 7 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 16 - 6 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 16 - 5 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 16 - 4 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 16 - 3 = 6 * (t + 2) + 1 by omega,
      show 6 * t + 16 - 2 = 6 * (t + 2) + 2 by omega,
      show 6 * t + 16 = 6 * (t + 2) + 4 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring
  · rw [show 6 * t + 17 - 13 = 6 * (t + 0) + 4 by omega,
      show 6 * t + 17 - 11 = 6 * (t + 1) + 0 by omega,
      show 6 * t + 17 - 10 = 6 * (t + 1) + 1 by omega,
      show 6 * t + 17 - 9 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 17 - 8 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 17 - 7 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 17 - 6 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 17 - 5 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 17 - 4 = 6 * (t + 2) + 1 by omega,
      show 6 * t + 17 - 3 = 6 * (t + 2) + 2 by omega,
      show 6 * t + 17 - 2 = 6 * (t + 2) + 3 by omega,
      show 6 * t + 17 = 6 * (t + 2) + 5 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring
  · rw [show 6 * t + 18 - 13 = 6 * (t + 0) + 5 by omega,
      show 6 * t + 18 - 11 = 6 * (t + 1) + 1 by omega,
      show 6 * t + 18 - 10 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 18 - 9 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 18 - 8 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 18 - 7 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 18 - 6 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 18 - 5 = 6 * (t + 2) + 1 by omega,
      show 6 * t + 18 - 4 = 6 * (t + 2) + 2 by omega,
      show 6 * t + 18 - 3 = 6 * (t + 2) + 3 by omega,
      show 6 * t + 18 - 2 = 6 * (t + 2) + 4 by omega,
      show 6 * t + 18 = 6 * (t + 3) + 0 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring
  · rw [show 6 * t + 19 - 13 = 6 * (t + 1) + 0 by omega,
      show 6 * t + 19 - 11 = 6 * (t + 1) + 2 by omega,
      show 6 * t + 19 - 10 = 6 * (t + 1) + 3 by omega,
      show 6 * t + 19 - 9 = 6 * (t + 1) + 4 by omega,
      show 6 * t + 19 - 8 = 6 * (t + 1) + 5 by omega,
      show 6 * t + 19 - 7 = 6 * (t + 2) + 0 by omega,
      show 6 * t + 19 - 6 = 6 * (t + 2) + 1 by omega,
      show 6 * t + 19 - 5 = 6 * (t + 2) + 2 by omega,
      show 6 * t + 19 - 4 = 6 * (t + 2) + 3 by omega,
      show 6 * t + 19 - 3 = 6 * (t + 2) + 4 by omega,
      show 6 * t + 19 - 2 = 6 * (t + 2) + 5 by omega,
      show 6 * t + 19 = 6 * (t + 3) + 1 by omega]
    simp only [OMA.k0, OMA.k1, OMA.k2, OMA.k3, OMA.k4, OMA.k5]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a057870.main := by
  refine ⟨?_, OMA.hrec⟩
  ext k
  rw [show ((1-X)^4*(1+X)^3*(1-X+X^2)*(1+X+X^2)^2 : PowerSeries ℚ) =
      1 - 2 • X ^ 2 - X ^ 3 + X ^ 4 + 2 • X ^ 5 - X ^ 6 - X ^ 7 + 2 • X ^ 8 + X ^ 9 - X ^ 10 - 2 • X ^ 11 + X ^ 13 by ring,
    show (X^2*(1+3*X+12*X^2+21*X^3+27*X^4+28*X^5+31*X^6+25*X^7+
        18*X^8+11*X^9+3*X^10) : PowerSeries ℚ) =
      X ^ 2 + 3 • X ^ 3 + 12 • X ^ 4 + 21 • X ^ 5 + 27 • X ^ 6 + 28 • X ^ 7 + 31 • X ^ 8 + 25 • X ^ 9 + 18 • X ^ 10 + 11 • X ^ 11 + 3 • X ^ 12 by ring]
  simp only [mul_add, mul_sub, mul_one, mul_smul_comm, map_add, map_sub, map_nsmul,
    coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  by_cases hk : k < 14
  · interval_cases k <;> norm_num [a]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 14 := ⟨k - 14, by omega⟩
    have h := OMA.hrec (m + 14) (by omega)
    simp only [show m + 14 - 2 = m + 12 from rfl,
      show m + 14 - 3 = m + 11 from rfl,
      show m + 14 - 4 = m + 10 from rfl,
      show m + 14 - 5 = m + 9 from rfl,
      show m + 14 - 6 = m + 8 from rfl,
      show m + 14 - 7 = m + 7 from rfl,
      show m + 14 - 8 = m + 6 from rfl,
      show m + 14 - 9 = m + 5 from rfl,
      show m + 14 - 10 = m + 4 from rfl,
      show m + 14 - 11 = m + 3 from rfl,
      show m + 14 - 13 = m + 1 from rfl] at h ⊢
    simp only [if_pos (show 2 ≤ m + 14 by omega),
      if_pos (show 3 ≤ m + 14 by omega),
      if_pos (show 4 ≤ m + 14 by omega),
      if_pos (show 5 ≤ m + 14 by omega),
      if_pos (show 6 ≤ m + 14 by omega),
      if_pos (show 7 ≤ m + 14 by omega),
      if_pos (show 8 ≤ m + 14 by omega),
      if_pos (show 9 ≤ m + 14 by omega),
      if_pos (show 10 ≤ m + 14 by omega),
      if_pos (show 11 ≤ m + 14 by omega),
      if_pos (show 13 ≤ m + 14 by omega),
      if_neg (show ¬ (m + 14 = 2) by omega),
      if_neg (show ¬ (m + 14 = 3) by omega),
      if_neg (show ¬ (m + 14 = 4) by omega),
      if_neg (show ¬ (m + 14 = 5) by omega),
      if_neg (show ¬ (m + 14 = 6) by omega),
      if_neg (show ¬ (m + 14 = 7) by omega),
      if_neg (show ¬ (m + 14 = 8) by omega),
      if_neg (show ¬ (m + 14 = 9) by omega),
      if_neg (show ¬ (m + 14 = 10) by omega),
      if_neg (show ¬ (m + 14 = 11) by omega),
      if_neg (show ¬ (m + 14 = 12) by omega),
      nsmul_eq_mul]
    push_cast
    linarith
