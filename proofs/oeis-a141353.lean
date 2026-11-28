import OMAStatements.S_oeis_a141353
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a141353.main := by
  have z (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    have := Nat.succ_mul_centralBinom_succ n
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    exact_mod_cast Nat.eq_of_mul_eq_mul_left n.succ_pos (by ring_nf at this ⊢; linarith)
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 := z (k + 1)
  have h2 := z (k + 2)
  have h3 := z (k + 3)
  simp only [OMA.S_oeis_a141353.a, show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega,
    zero_pow (Nat.succ_ne_zero _)]
  push_cast at *
  linear_combination h3 - 4 * h2 + 4 * h1
