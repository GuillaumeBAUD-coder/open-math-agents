import OMAStatements.S_oeis_a295320

theorem OMA.aux_even (k : ℕ) : ∀ M : ℕ, M ≤ k →
    3 * (∑ i ∈ Finset.Icc 1 (2 * M), i * (2 * k - i) * ((2 * k - i) % 2)) + 4 * M * M * (M + 1)
      = 3 * (2 * k + 1) * M * M + M * (M + 1) := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    have ih' := ih (by omega)
    obtain ⟨t, rfl⟩ : ∃ t, k = M + 1 + t := ⟨k - (M + 1), by omega⟩
    have e1 : 2 * (M + 1) = 2 * M + 1 + 1 := by ring
    rw [e1, Finset.sum_Icc_succ_top (a := 1) (b := 2 * M + 1) (by omega),
      Finset.sum_Icc_succ_top (a := 1) (b := 2 * M) (by omega)]
    have h1 : 2 * (M + 1 + t) - (2 * M + 1) = 2 * t + 1 := by omega
    have h2 : 2 * (M + 1 + t) - (2 * M + 1 + 1) = 2 * t := by omega
    have h3 : (2 * t + 1) % 2 = 1 := by omega
    have h4 : (2 * t) % 2 = 0 := by omega
    rw [h1, h2, h3, h4]
    nlinarith [ih']

theorem OMA.aux_odd (k : ℕ) : ∀ M : ℕ, M ≤ k →
    3 * (∑ i ∈ Finset.Icc 1 (2 * M), i * (2 * k + 1 - i) * ((2 * k + 1 - i) % 2))
        + 2 * M * (M + 1) * (2 * M + 1)
      = 3 * (2 * k + 1) * M * (M + 1) := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    have ih' := ih (by omega)
    obtain ⟨t, rfl⟩ : ∃ t, k = M + 1 + t := ⟨k - (M + 1), by omega⟩
    have e1 : Finset.Icc 1 (2 * (M + 1)) = Finset.Icc 1 (2 * M + 1 + 1) := by
      congr 1
    rw [e1, Finset.sum_Icc_succ_top (a := 1) (b := 2 * M + 1) (by omega),
      Finset.sum_Icc_succ_top (a := 1) (b := 2 * M) (by omega)]
    have h1 : 2 * (M + 1 + t) + 1 - (2 * M + 1) = 2 * t + 2 := by omega
    have h2 : 2 * (M + 1 + t) + 1 - (2 * M + 1 + 1) = 2 * t + 1 := by omega
    have h3 : (2 * t + 2) % 2 = 0 := by omega
    have h4 : (2 * t + 1) % 2 = 1 := by omega
    rw [h1, h2, h3, h4]
    nlinarith [ih']

theorem OMA.c0 (m : ℕ) :
    3 * (OMA.S_oeis_a295320.a (4 * m) : ℤ) = m * (8 * m ^ 2 + 1) := by
  have key : 3 * OMA.S_oeis_a295320.a (4 * m) + 4 * m * m * (m + 1)
      = 3 * (4 * m + 1) * m * m + m * (m + 1) := by
    have h := OMA.aux_even (2 * m) m (by omega)
    rw [show 2 * (2 * m) = 4 * m by ring] at h
    rcases m with _ | m
    · simp [OMA.S_oeis_a295320.a]
    · unfold OMA.S_oeis_a295320.a
      have e : (4 * (m + 1) - 1) / 2 = 2 * m + 1 := by omega
      have e2 : Finset.Icc 1 (2 * (m + 1)) = Finset.Icc 1 (2 * m + 1 + 1) := by
        congr 1
      rw [e2, Finset.sum_Icc_succ_top (a := 1) (b := 2 * m + 1) (by omega)] at h
      have z : (4 * (m + 1) - (2 * m + 1 + 1)) % 2 = 0 := by omega
      rw [z, mul_zero, add_zero] at h
      rw [e]
      exact h
  have key' : (3 * (OMA.S_oeis_a295320.a (4 * m) : ℤ) + 4 * m * m * (m + 1))
      = 3 * (4 * m + 1) * m * m + m * (m + 1) := by exact_mod_cast key
  linear_combination key'

theorem OMA.c2 (m : ℕ) :
    3 * (OMA.S_oeis_a295320.a (4 * m + 2) : ℤ) = m * (2 * m + 1) * (4 * m + 1) := by
  have key : 3 * OMA.S_oeis_a295320.a (4 * m + 2) + 4 * m * m * (m + 1)
      = 3 * (4 * m + 2 + 1) * m * m + m * (m + 1) := by
    have h := OMA.aux_even (2 * m + 1) m (by omega)
    rw [show 2 * (2 * m + 1) = 4 * m + 2 by ring] at h
    unfold OMA.S_oeis_a295320.a
    have e : (4 * m + 2 - 1) / 2 = 2 * m := by omega
    rw [e]
    exact h
  have key' : (3 * (OMA.S_oeis_a295320.a (4 * m + 2) : ℤ) + 4 * m * m * (m + 1))
      = 3 * (4 * m + 2 + 1) * m * m + m * (m + 1) := by exact_mod_cast key
  linear_combination key'

theorem OMA.c1 (m : ℕ) :
    3 * (OMA.S_oeis_a295320.a (4 * m + 1) : ℤ) = m * (m + 1) * (8 * m + 1) := by
  have key : 3 * OMA.S_oeis_a295320.a (4 * m + 1) + 2 * m * (m + 1) * (2 * m + 1)
      = 3 * (4 * m + 1) * m * (m + 1) := by
    have h := OMA.aux_odd (2 * m) m (by omega)
    rw [show 2 * (2 * m) = 4 * m by ring] at h
    unfold OMA.S_oeis_a295320.a
    have e : (4 * m + 1 - 1) / 2 = 2 * m := by omega
    rw [e]
    exact h
  have key' : (3 * (OMA.S_oeis_a295320.a (4 * m + 1) : ℤ) + 2 * m * (m + 1) * (2 * m + 1))
      = 3 * (4 * m + 1) * m * (m + 1) := by exact_mod_cast key
  linear_combination key'

theorem OMA.c3 (m : ℕ) :
    3 * (OMA.S_oeis_a295320.a (4 * m + 3) : ℤ) = m * (m + 1) * (8 * m + 7) := by
  have key : 3 * OMA.S_oeis_a295320.a (4 * m + 3) + 2 * m * (m + 1) * (2 * m + 1)
      = 3 * (4 * m + 3) * m * (m + 1) := by
    have h := OMA.aux_odd (2 * m + 1) m (by omega)
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 by ring] at h
    unfold OMA.S_oeis_a295320.a
    have e : (4 * m + 3 - 1) / 2 = 2 * m + 1 := by omega
    rw [e, Finset.sum_Icc_succ_top (a := 1) (b := 2 * m) (by omega)]
    have z : (4 * m + 3 - (2 * m + 1)) % 2 = 0 := by omega
    rw [z, mul_zero, add_zero]
    exact h
  have key' : (3 * (OMA.S_oeis_a295320.a (4 * m + 3) : ℤ) + 2 * m * (m + 1) * (2 * m + 1))
      = 3 * (4 * m + 3) * m * (m + 1) := by exact_mod_cast key
  linear_combination key'

theorem OMA.solution : type_of% @OMA.S_oeis_a295320.main := by
  intro n hn
  obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 4 ∧ n = 4 * p + r + 13 :=
    ⟨(n - 13) / 4, (n - 13) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  · -- n = 4(p+3)+1
    have e0 : 4 * p + 0 + 13 = 4 * (p + 3) + 1 := by omega
    have e1 : 4 * p + 0 + 13 - 1 = 4 * (p + 3) := by omega
    have e4 : 4 * p + 0 + 13 - 4 = 4 * (p + 2) + 1 := by omega
    have e5 : 4 * p + 0 + 13 - 5 = 4 * (p + 2) := by omega
    have e8 : 4 * p + 0 + 13 - 8 = 4 * (p + 1) + 1 := by omega
    have e9 : 4 * p + 0 + 13 - 9 = 4 * (p + 1) := by omega
    have e12 : 4 * p + 0 + 13 - 12 = 4 * p + 1 := by omega
    have e13 : 4 * p + 0 + 13 - 13 = 4 * p := by omega
    rw [e1, e4, e5, e8, e9, e12, e13, e0]
    have a0 := OMA.c1 (p + 3)
    have a1 := OMA.c0 (p + 3)
    have a4 := OMA.c1 (p + 2)
    have a5 := OMA.c0 (p + 2)
    have a8 := OMA.c1 (p + 1)
    have a9 := OMA.c0 (p + 1)
    have a12 := OMA.c1 p
    have a13 := OMA.c0 p
    push_cast at a0 a1 a4 a5 a8 a9 a12 a13
    linarith
  · -- n = 4(p+3)+2
    have e0 : 4 * p + 1 + 13 = 4 * (p + 3) + 2 := by omega
    have e1 : 4 * p + 1 + 13 - 1 = 4 * (p + 3) + 1 := by omega
    have e4 : 4 * p + 1 + 13 - 4 = 4 * (p + 2) + 2 := by omega
    have e5 : 4 * p + 1 + 13 - 5 = 4 * (p + 2) + 1 := by omega
    have e8 : 4 * p + 1 + 13 - 8 = 4 * (p + 1) + 2 := by omega
    have e9 : 4 * p + 1 + 13 - 9 = 4 * (p + 1) + 1 := by omega
    have e12 : 4 * p + 1 + 13 - 12 = 4 * p + 2 := by omega
    have e13 : 4 * p + 1 + 13 - 13 = 4 * p + 1 := by omega
    rw [e1, e4, e5, e8, e9, e12, e13, e0]
    have a0 := OMA.c2 (p + 3)
    have a1 := OMA.c1 (p + 3)
    have a4 := OMA.c2 (p + 2)
    have a5 := OMA.c1 (p + 2)
    have a8 := OMA.c2 (p + 1)
    have a9 := OMA.c1 (p + 1)
    have a12 := OMA.c2 p
    have a13 := OMA.c1 p
    push_cast at a0 a1 a4 a5 a8 a9 a12 a13
    linarith
  · -- n = 4(p+3)+3
    have e0 : 4 * p + 2 + 13 = 4 * (p + 3) + 3 := by omega
    have e1 : 4 * p + 2 + 13 - 1 = 4 * (p + 3) + 2 := by omega
    have e4 : 4 * p + 2 + 13 - 4 = 4 * (p + 2) + 3 := by omega
    have e5 : 4 * p + 2 + 13 - 5 = 4 * (p + 2) + 2 := by omega
    have e8 : 4 * p + 2 + 13 - 8 = 4 * (p + 1) + 3 := by omega
    have e9 : 4 * p + 2 + 13 - 9 = 4 * (p + 1) + 2 := by omega
    have e12 : 4 * p + 2 + 13 - 12 = 4 * p + 3 := by omega
    have e13 : 4 * p + 2 + 13 - 13 = 4 * p + 2 := by omega
    rw [e1, e4, e5, e8, e9, e12, e13, e0]
    have a0 := OMA.c3 (p + 3)
    have a1 := OMA.c2 (p + 3)
    have a4 := OMA.c3 (p + 2)
    have a5 := OMA.c2 (p + 2)
    have a8 := OMA.c3 (p + 1)
    have a9 := OMA.c2 (p + 1)
    have a12 := OMA.c3 p
    have a13 := OMA.c2 p
    push_cast at a0 a1 a4 a5 a8 a9 a12 a13
    linarith
  · -- n = 4(p+4)
    have e0 : 4 * p + 3 + 13 = 4 * (p + 4) := by omega
    have e1 : 4 * p + 3 + 13 - 1 = 4 * (p + 3) + 3 := by omega
    have e4 : 4 * p + 3 + 13 - 4 = 4 * (p + 3) := by omega
    have e5 : 4 * p + 3 + 13 - 5 = 4 * (p + 2) + 3 := by omega
    have e8 : 4 * p + 3 + 13 - 8 = 4 * (p + 2) := by omega
    have e9 : 4 * p + 3 + 13 - 9 = 4 * (p + 1) + 3 := by omega
    have e12 : 4 * p + 3 + 13 - 12 = 4 * (p + 1) := by omega
    have e13 : 4 * p + 3 + 13 - 13 = 4 * p + 3 := by omega
    rw [e1, e4, e5, e8, e9, e12, e13, e0]
    have a0 := OMA.c0 (p + 4)
    have a1 := OMA.c3 (p + 3)
    have a4 := OMA.c0 (p + 3)
    have a5 := OMA.c3 (p + 2)
    have a8 := OMA.c0 (p + 2)
    have a9 := OMA.c3 (p + 1)
    have a12 := OMA.c0 (p + 1)
    have a13 := OMA.c3 p
    push_cast at a0 a1 a4 a5 a8 a9 a12 a13
    linarith
