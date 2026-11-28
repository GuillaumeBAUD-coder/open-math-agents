import OMAReductions.R_mo_144208_R1

private lemma three_pow_mod_eight (n : ℕ) : 3 ^ n % 8 = 1 ∨ 3 ^ n % 8 = 3 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide

private lemma tail_lt_four_pow {a : ℕ} (ha : 2 ≤ a) : 1 + 2 ^ a + 3 ^ a < 4 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    rw [pow_succ, pow_succ, pow_succ]
    omega

theorem OMA.solution : OMA.R_mo_144208_R1.H3 := by
  intro a b c ha hb hc heq
  rcases lt_or_ge b 3 with hb3 | hb3
  · have hb2 : b = 2 := by omega
    subst hb2
    rcases lt_or_ge a 2 with ha2 | ha2
    · have ha1 : a = 1 := by omega
      subst ha1
      rcases lt_or_ge c 4 with hc4 | hc4
      · have hc3 : c = 3 := by omega
        subst hc3
        rfl
      · have h256 : 256 ≤ 1 + 2 ^ c + 3 ^ c + 4 ^ c :=
          (show 256 ≤ 4 ^ 4 by decide).trans
            ((Nat.pow_le_pow_right (by decide) hc4).trans
              (Nat.le_add_left (4 ^ c) (1 + 2 ^ c + 3 ^ c)))
        rw [← heq] at h256
        exact absurd h256 (by decide)
    · have hlt : 1 + 2 ^ a + 3 ^ a + 4 ^ a < 2 * 4 ^ a := by
        have := tail_lt_four_pow ha2
        omega
      have hsq : (1 + 2 ^ a + 3 ^ a + 4 ^ a) ^ 2 < 4 ^ (2 * a + 1) := by
        calc (1 + 2 ^ a + 3 ^ a + 4 ^ a) ^ 2
            < (2 * 4 ^ a) ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
          _ = 4 * (4 ^ a) ^ 2 := by ring
          _ = 4 * 4 ^ (a * 2) := by rw [← pow_mul]
          _ = 4 ^ (2 * a + 1) := by rw [mul_comm a 2, pow_succ']
      have hc' : 2 * a + 1 ≤ c := by omega
      have h4c : 4 ^ (2 * a + 1) ≤ 1 + 2 ^ c + 3 ^ c + 4 ^ c :=
        (Nat.pow_le_pow_right (by decide) hc').trans
          (Nat.le_add_left (4 ^ c) (1 + 2 ^ c + 3 ^ c))
      exact absurd heq (lt_of_lt_of_le hsq h4c).ne
  · exfalso
    have hc3 : 3 ≤ c := by
      have : 1 * 3 ≤ a * b := Nat.mul_le_mul ha hb3
      omega
    have hS2 : (1 + 2 ^ a + 3 ^ a + 4 ^ a) % 2 = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
      have hsplit : 1 + 2 ^ (k + 1) + 3 ^ (k + 1) + 4 ^ (k + 1) =
          (1 + 3 ^ (k + 1)) + 2 * (2 ^ k + 2 * 4 ^ k) := by ring
      rw [hsplit]
      rcases three_pow_mod_eight (k + 1) with h3 | h3 <;> omega
    obtain ⟨m, hm⟩ : ∃ m, 1 + 2 ^ a + 3 ^ a + 4 ^ a = 2 * m :=
      ⟨(1 + 2 ^ a + 3 ^ a + 4 ^ a) / 2, by omega⟩
    have hlhs : (1 + 2 ^ a + 3 ^ a + 4 ^ a) ^ b % 8 = 0 := by
      obtain ⟨d, rfl⟩ : ∃ d, b = d + 3 := ⟨b - 3, by omega⟩
      have h8 : (2 * m) ^ (d + 3) = 8 * (m ^ 3 * (2 * m) ^ d) := by ring
      rw [hm, h8]
      omega
    have hrhs : (1 + 2 ^ c + 3 ^ c + 4 ^ c) % 8 ≠ 0 := by
      obtain ⟨e, rfl⟩ : ∃ e, c = e + 3 := ⟨c - 3, by omega⟩
      have hsplit : 1 + 2 ^ (e + 3) + 3 ^ (e + 3) + 4 ^ (e + 3) =
          (1 + 3 ^ (e + 3)) + 8 * (2 ^ e + 8 * 4 ^ e) := by ring
      rw [hsplit]
      rcases three_pow_mod_eight (e + 3) with h3 | h3 <;> omega
    rw [heq] at hlhs
    exact hrhs hlhs
