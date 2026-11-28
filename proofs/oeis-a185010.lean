import OMAStatements.S_oeis_a185010
import Mathlib

open OMA.S_oeis_a185010

lemma catalan_step (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have hc0 := succ_mul_catalan_eq_centralBinom n
  have hc1 := succ_mul_catalan_eq_centralBinom (n + 1)
  rw [hc1]
  apply Nat.mul_left_cancel (Nat.succ_pos n)
  calc
    (n + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n :=
      Nat.succ_mul_centralBinom_succ n
    _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [← hc0]
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring

lemma recurrence_shifted (k : ℕ) :
    ((k : ℤ) + 2) * ((k : ℤ) + 3) * (a (k + 2) : ℤ) -
      4 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * (a (k + 1) : ℤ) -
      12 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 1) * (a k : ℤ) = 0 := by
  have hc0 : (((k + 2) * catalan (k + 1) : ℕ) : ℤ) =
      ((2 * (2 * k + 1) * catalan k : ℕ) : ℤ) := by
    exact_mod_cast catalan_step k
  have hc1 : (((k + 3) * catalan (k + 2) : ℕ) : ℤ) =
      ((2 * (2 * k + 3) * catalan (k + 1) : ℕ) : ℤ) := by
    exact_mod_cast catalan_step (k + 1)
  have hb : (b (k + 3) : ℤ) = 2 * (b (k + 2) : ℤ) + 3 * (b (k + 1) : ℤ) := by
    exact_mod_cast (rfl : b (k + 3) = 2 * b (k + 2) + 3 * b (k + 1))
  push_cast at hc0 hc1
  simp only [a, Nat.cast_mul]
  linear_combination
    ((k : ℤ) + 2) * (b (k + 3) : ℤ) * hc1 +
      2 * ((k : ℤ) + 2) * (2 * (k : ℤ) + 3) * (catalan (k + 1) : ℤ) * hb +
      6 * (2 * (k : ℤ) + 3) * (b (k + 1) : ℤ) * hc0

theorem OMA.solution : type_of% @OMA.S_oeis_a185010.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  have hk := recurrence_shifted k
  push_cast at hk ⊢
  linear_combination hk
