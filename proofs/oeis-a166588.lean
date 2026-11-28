import OMAStatements.S_oeis_a166588
import Mathlib

namespace A166588Aux

lemma catalan_rec (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h4 : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc (k + 1) * ((k + 2) * catalan (k + 1))
        = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by ring
      _ = (k + 1) * Nat.centralBinom (k + 1) := by rw [h1]
      _ = 2 * (2 * k + 1) * Nat.centralBinom k := h3
      _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) h4

open OMA.S_oeis_a166588 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + b (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a166588 in
lemma b_rec (m : ℕ) : ((m : ℤ) + 4) * b (m + 3) = 4 * ((m : ℤ) + 1) * b (m + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have e1 : b (2 * k + 3) = (catalan (k + 1) : ℤ) := by
      unfold b
      rw [if_neg (by omega), if_pos (by omega), show (2 * k + 3 - 1) / 2 = k + 1 by omega]
    have e2 : b (2 * k + 1) = (catalan k : ℤ) := by
      unfold b
      rw [if_neg (by omega), if_pos (by omega), show (2 * k + 1 - 1) / 2 = k by omega]
    rw [e1, e2]
    have h := catalan_rec k
    have h' : ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
      exact_mod_cast h
    push_cast
    linear_combination 2 * h'
  · have e1 : b (2 * k + 1 + 3) = 0 := by
      unfold b
      rw [if_neg (by omega), if_neg (by omega)]
    have e2 : b (2 * k + 1 + 1) = 0 := by
      unfold b
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e1, e2]
    ring

end A166588Aux

open OMA.S_oeis_a166588 A166588Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a166588.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have h1 : a (m + 3) = a (m + 2) + b (m + 3) := a_succ (m + 2)
  have h2 : a (m + 1) = a m + b (m + 1) := a_succ m
  have h3 := b_rec m
  rw [h1, h2]
  push_cast
  linear_combination -h3
