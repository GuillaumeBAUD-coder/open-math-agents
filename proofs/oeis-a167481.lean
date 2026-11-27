import OMAStatements.S_oeis_a167481
import Mathlib

namespace A167481aux

open OMA.S_oeis_a167481 in
lemma step (n : ℕ) : a (n + 1) = -2 * a n + ((2 * (n + 1)).choose (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  · simp

open OMA.S_oeis_a167481 in
lemma central (m : ℕ) : ((m : ℤ) + 2) * ((2 * (m + 1 + 1)).choose (m + 1 + 1) : ℤ)
    = (4 * (m : ℤ) + 6) * ((2 * (m + 1)).choose (m + 1) : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ (m + 1)
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : (((m + 1 + 1) * (2 * (m + 1 + 1)).choose (m + 1 + 1) : ℕ) : ℤ)
      = ((2 * (2 * (m + 1) + 1) * (2 * (m + 1)).choose (m + 1) : ℕ) : ℤ) := by
    rw [h]
  push_cast at h'
  linarith

end A167481aux

theorem OMA.solution : type_of% @OMA.S_oeis_a167481.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show m + 2 = m + 1 + 1 by ring, A167481aux.step (m + 1), A167481aux.step m]
  push_cast
  linear_combination A167481aux.central m
