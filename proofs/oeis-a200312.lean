import OMAStatements.S_oeis_a200312

namespace OMA.S_oeis_a200312

lemma cat_rec (k : ℕ) : ((k + 2 : ℕ) : ℤ) * (catalan (k + 1) : ℤ) =
    2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * Nat.centralBinom (k + 1) := by
          rw [← h1]
      _ = 2 * (2 * k + 1) * Nat.centralBinom k := h3
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by rw [← h2]; ring
  have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) this
  exact_mod_cast this

theorem solution_main :
    ∀ n : ℕ, 2 ≤ n →
      (n : ℤ) * ((n : ℤ) + 1) * (a n : ℤ) -
        2 * (n : ℤ) * (2 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
        12 * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, a]
  have hb : (b (k + 2) : ℤ) = b (k + 1) + 3 * b k := by simp [b]
  have c1 := cat_rec (k + 1)
  have c0 := cat_rec k
  push_cast at c1 c0 hb ⊢
  rw [hb]
  linear_combination
    ((k : ℤ) + 2) * ((b (k + 1) : ℤ) + 3 * (b k : ℤ)) * c1 +
      6 * (2 * (k : ℤ) + 3) * (b k : ℤ) * c0
end OMA.S_oeis_a200312

theorem OMA.solution : type_of% @OMA.S_oeis_a200312.main := OMA.S_oeis_a200312.solution_main
