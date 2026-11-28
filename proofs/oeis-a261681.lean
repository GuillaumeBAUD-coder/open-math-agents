import OMAStatements.S_oeis_a261681

theorem OMA.solution : type_of% @OMA.S_oeis_a261681.main := by
  have ha : ∀ m h : ℕ, m / 2 = h →
      OMA.S_oeis_a261681.a m = 2 ^ m + (m.choose h : ℤ) - 1 := by
    intro m h e
    subst e
    rfl
  have hA : ∀ m m' k c : ℕ, m' = m + 1 → m' - k = c →
      (m.choose k : ℤ) * (m' : ℤ) = (m'.choose k : ℤ) * (c : ℤ) := by
    intro m m' k c e1 e2
    subst e1
    subst e2
    exact_mod_cast Nat.choose_mul_succ_eq m k
  have hB : ∀ m m' m'' k : ℕ, m' = 2 * m + 1 → m'' = 2 * m + 2 → k = m + 1 →
      (m''.choose k : ℤ) = 2 * (m'.choose m : ℤ) := by
    intro m m' m'' k e1 e2 e3
    subst e1
    subst e2
    subst e3
    have h1 : (2 * m + 2).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) :=
      Nat.choose_succ_succ' (2 * m + 1) m
    have h2 : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := Nat.choose_symm_half m
    have h3 : (2 * m + 2).choose (m + 1) = 2 * (2 * m + 1).choose m := by omega
    exact_mod_cast h3
  intro n hn
  rcases Nat.even_or_odd' n with ⟨i, hi | hi⟩
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 4 := ⟨i - 2, by omega⟩
    have A1 := hA (2 * j) (2 * j + 1) j (j + 1) (by omega) (by omega)
    have A3 := hA (2 * j + 2) (2 * j + 3) (j + 1) (j + 2) (by omega) (by omega)
    have B2 := hB j (2 * j + 1) (2 * j + 2) (j + 1) (by omega) (by omega) (by omega)
    have B4 := hB (j + 1) (2 * j + 3) (2 * j + 4) (j + 2) (by omega) (by omega) (by omega)
    have s1 : 2 * j + 4 - 1 = 2 * j + 3 := by omega
    have s2 : 2 * j + 4 - 2 = 2 * j + 2 := by omega
    have s3 : 2 * j + 4 - 3 = 2 * j + 1 := by omega
    have s4 : 2 * j + 4 - 4 = 2 * j := by omega
    rw [s1, s2, s3, s4, ha (2 * j + 4) (j + 2) (by omega), ha (2 * j + 3) (j + 1) (by omega),
      ha (2 * j + 2) (j + 1) (by omega), ha (2 * j + 1) j (by omega), ha (2 * j) j (by omega)]
    push_cast at A1 A3 ⊢
    linear_combination (-(2 * (j : ℤ) + 5) * (2 * j)) * B4 - 2 * (2 * (j : ℤ) + 1) * A3
      + (16 * (j : ℤ) ^ 2 + 12 * j - 2) * B2 + 8 * (2 * (j : ℤ) + 1) * A1
  · obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 5 := ⟨i - 2, by omega⟩
    have A3 := hA (2 * j + 2) (2 * j + 3) (j + 1) (j + 2) (by omega) (by omega)
    have A5 := hA (2 * j + 4) (2 * j + 5) (j + 2) (j + 3) (by omega) (by omega)
    have B2 := hB j (2 * j + 1) (2 * j + 2) (j + 1) (by omega) (by omega) (by omega)
    have B4 := hB (j + 1) (2 * j + 3) (2 * j + 4) (j + 2) (by omega) (by omega) (by omega)
    have s1 : 2 * j + 5 - 1 = 2 * j + 4 := by omega
    have s2 : 2 * j + 5 - 2 = 2 * j + 3 := by omega
    have s3 : 2 * j + 5 - 3 = 2 * j + 2 := by omega
    have s4 : 2 * j + 5 - 4 = 2 * j + 1 := by omega
    rw [s1, s2, s3, s4, ha (2 * j + 5) (j + 2) (by omega), ha (2 * j + 4) (j + 2) (by omega),
      ha (2 * j + 3) (j + 1) (by omega), ha (2 * j + 2) (j + 1) (by omega),
      ha (2 * j + 1) j (by omega)]
    push_cast at A3 A5 ⊢
    linear_combination 2 * (2 * (j : ℤ) + 1) * A5 + (4 * (j : ℤ) ^ 2 + 18 * j + 12) * B4
      - 8 * (2 * (j : ℤ) + 1) * A3 - 16 * ((j : ℤ) + 1) ^ 2 * B2
