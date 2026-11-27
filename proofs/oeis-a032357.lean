import OMAStatements.S_oeis_a032357

-- Problem: A032357, the conjectured recurrence holds.
-- Credit: @bnb9001

namespace OMA_A032357_Proof

open OMA.S_oeis_a032357

lemma a_succ (n : ℕ) : a (n + 1) = catalan (n + 1) - a n := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + 1 - k) * (catalan k : ℤ) =
      - ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (catalan k : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  rw [this]
  ring

lemma catalan_rec (m : ℕ) : ((m + 2 : ℕ) : ℤ) * catalan (m + 1) = 2 * (2 * m + 1) * catalan m := by
  have h1 := succ_mul_catalan_eq_centralBinom (m + 1)
  have h2 := succ_mul_catalan_eq_centralBinom m
  have h3 := Nat.succ_mul_centralBinom_succ m
  have key : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * (2 * (2 * m + 1) * catalan m) := by
    rw [show m + 1 + 1 = m + 2 by ring] at h1
    rw [h1, h3, ← h2]
    ring
  have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) key
  exact_mod_cast this

end OMA_A032357_Proof

open OMA_A032357_Proof OMA.S_oeis_a032357 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032357.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [a_succ (m + 1)]
  have h := a_succ m
  have hc := catalan_rec (m + 1)
  push_cast at hc h ⊢
  linear_combination hc - (4 * (m : ℤ) + 6) * h
