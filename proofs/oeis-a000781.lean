import OMAStatements.S_oeis_a000781

namespace OMA.P_a000781

open OMA.S_oeis_a000781

lemma cat_rec (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * Nat.centralBinom (k + 1) := by
            rw [← h1]
      _ = 2 * (2 * k + 1) * Nat.centralBinom k := h3
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by rw [← h2]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

lemma cat_pos (k : ℕ) : 0 < catalan k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := cat_rec k
    have : 0 < (k + 2) * catalan (k + 1) := by rw [h]; positivity
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at this

lemma cat_mono (k : ℕ) : catalan k ≤ catalan (k + 1) := by
  have := cat_rec k
  nlinarith

lemma a_cast (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 3 * (catalan n : ℤ) - catalan (n - 1) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 := cat_mono k
  have h2 := cat_pos (k + 1)
  obtain ⟨d, hd⟩ : ∃ d, 3 * catalan (k + 1) = catalan k + 1 + d := ⟨3 * catalan (k + 1) - catalan k - 1, by omega⟩
  have ha : a (k + 1) = d := by simp only [a, Nat.add_sub_cancel]; omega
  rw [ha, Nat.add_sub_cancel]
  have : ((3 * catalan (k + 1) : ℕ) : ℤ) = ((catalan k + 1 + d : ℕ) : ℤ) := by rw [hd]
  push_cast at this
  linarith

lemma cat_rec_int (k : ℕ) :
    ((k : ℤ) + 2) * catalan (k + 1) = 2 * (2 * (k : ℤ) + 1) * catalan k := by
  exact_mod_cast cat_rec k

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      3 * ((n : ℤ) + 1) * (a n : ℤ) +
        (-19 * (n : ℤ) + 7) * (a (n - 1) : ℤ) +
        (33 * (n : ℤ) - 53) * (a (n - 2) : ℤ) +
        (-21 * (n : ℤ) + 61) * (a (n - 3) : ℤ) +
        2 * (2 * (n : ℤ) - 9) * (a (n - 4) : ℤ) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [a_cast _ (by omega), a_cast _ (by omega), a_cast _ (by omega), a_cast _ (by omega),
    a_cast _ (by omega)]
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega,
    show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
  have r0 := cat_rec_int m
  have r1 := cat_rec_int (m + 1)
  have r2 := cat_rec_int (m + 2)
  have r3 := cat_rec_int (m + 3)
  have r4 := cat_rec_int (m + 4)
  push_cast at r0 r1 r2 r3 r4 ⊢
  linear_combination 9 * r4 - 24 * r3 + 22 * r2 - 8 * r1 + r0

end OMA.P_a000781

theorem OMA.solution : type_of% @OMA.S_oeis_a000781.main := OMA.P_a000781.main
