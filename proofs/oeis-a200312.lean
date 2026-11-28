import OMAStatements.S_oeis_a200312
import Mathlib

open OMA.S_oeis_a200312 in
theorem OMA.solution : type_of% @OMA.S_oeis_a200312.main := by
  have z (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    have := Nat.succ_mul_centralBinom_succ n
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left n.succ_pos (by ring_nf at this ⊢; linarith)
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have c1 := z (k + 1)
  have c0 := z k
  simp only [a, b, show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  push_cast at *
  linear_combination ((k : ℤ) + 2) * ((b (k + 1) : ℤ) + 3 * (b k : ℤ)) * c1 +
    6 * (2 * (k : ℤ) + 3) * (b k : ℤ) * c0
