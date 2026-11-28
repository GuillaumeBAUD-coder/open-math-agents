import OMAStatements.S_oeis_a051960
import Mathlib

open OMA.S_oeis_a051960 in
theorem OMA.solution : type_of% @OMA.S_oeis_a051960.main := by
  have r (k : ℕ) : ((k : ℤ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    have h := Nat.succ_mul_centralBinom_succ k
    rw [← succ_mul_catalan_eq_centralBinom (k + 1), ← succ_mul_catalan_eq_centralBinom k] at h
    have : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      nlinarith only [h]
    exact_mod_cast Nat.eq_of_mul_eq_mul_left k.succ_pos this
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, a]
  have h1 := r (k + 1)
  have h0 := r k
  push_cast at h1 h0 ⊢
  linear_combination (3 * (k : ℤ) + 8) * h1 + 2 * (3 * (k : ℤ) + 2) * h0
