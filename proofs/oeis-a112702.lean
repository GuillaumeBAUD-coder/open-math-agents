import OMAStatements.S_oeis_a112702
import Mathlib

open OMA.S_oeis_a112702 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112702.main := by
  have r (k : ℕ) : ((k : ℤ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
    have h := Nat.succ_mul_centralBinom_succ k
    rw [← succ_mul_catalan_eq_centralBinom (k + 1), ← succ_mul_catalan_eq_centralBinom k] at h
    have : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      nlinarith only [h]
    exact_mod_cast Nat.eq_of_mul_eq_mul_left k.succ_pos this
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega, a,
    Finset.sum_range_succ (n := k + 2), Finset.sum_range_succ (n := k + 1)]
  have h := r (k + 1)
  push_cast at h ⊢
  linear_combination 8 ^ (k + 2) * h
