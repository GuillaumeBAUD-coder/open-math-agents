import OMAStatements.S_oeis_a155587
import Mathlib

open PowerSeries OMA.S_oeis_a155587 in
theorem OMA.solution : type_of% @OMA.S_oeis_a155587.main := by
  have z (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    have := Nat.succ_mul_centralBinom_succ n
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left n.succ_pos (by ring_nf at this ⊢; linarith)
  have e (n : ℕ) : a n = ∑ j ∈ Finset.range (n + 1), coeff j (1 + X * c) := by
    unfold a
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_mk, mul_one]
  have s (m : ℕ) : a (m + 1) = a m + (catalan m : ℤ) := by
    rw [e, e m, Finset.sum_range_succ (n := m + 1), map_add, coeff_succ_X_mul, coeff_one]
    simp [c, coeff_mk]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show m + 2 = m + 1 + 1 from rfl, s (m + 1), s m]
  have h := z m
  push_cast at h ⊢
  linear_combination h
