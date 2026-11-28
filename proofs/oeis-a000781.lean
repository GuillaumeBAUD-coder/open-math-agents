import OMAStatements.S_oeis_a000781
import Mathlib

open OMA.S_oeis_a000781 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000781.main := by
  have r (k : ℕ) : ((k : ℤ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    have h := Nat.succ_mul_centralBinom_succ k
    rw [← succ_mul_catalan_eq_centralBinom (k + 1), ← succ_mul_catalan_eq_centralBinom k] at h
    have : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      nlinarith only [h]
    exact_mod_cast Nat.eq_of_mul_eq_mul_left k.succ_pos this
  have c (n : ℕ) : (a (n + 1) : ℤ) = 3 * catalan (n + 1) - catalan n - 1 := by
    have : 0 < catalan (n + 1) := by
      nlinarith [Nat.centralBinom_pos (n + 1), succ_mul_catalan_eq_centralBinom (n + 1)]
    have : (catalan n : ℤ) ≤ catalan (n + 1) := by nlinarith [r n]
    simp only [a, Nat.add_sub_cancel]
    omega
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [Nat.reduceSubDiff, c]
  have h0 := r m
  have h1 := r (m + 1)
  have h2 := r (m + 2)
  have h3 := r (m + 3)
  have h4 := r (m + 4)
  push_cast at *
  linear_combination 9 * h4 - 24 * h3 + 22 * h2 - 8 * h1 + h0
