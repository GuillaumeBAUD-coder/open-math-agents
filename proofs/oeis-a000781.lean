import OMAStatements.S_oeis_a000781
open OMA.S_oeis_a000781
theorem OMA.solution : type_of% @OMA.S_oeis_a000781.main := by
  have s (n : ℕ) : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_left n.succ_pos
    have := Nat.succ_mul_centralBinom_succ n
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at this
    ring_nf at this ⊢
    linarith
  have z (n : ℕ) : ((n : ℤ) + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by exact_mod_cast s n
  have c (n : ℕ) : (a (n + 1) : ℤ) = 3 * catalan (n + 1) - catalan n - 1 := by
    have h := s n
    have := succ_mul_catalan_eq_centralBinom (n + 1)
    have := Nat.centralBinom_pos (n + 1)
    have : 0 < catalan (n + 1) := by nlinarith
    have : catalan n ≤ catalan (n + 1) := by nlinarith
    simp only [a, Nat.add_sub_cancel]
    omega
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    c (m + 4), c (m + 3), c (m + 2), c (m + 1), c m]
  have h0 := z m
  have h1 := z (m + 1)
  have h2 := z (m + 2)
  have h3 := z (m + 3)
  have h4 := z (m + 4)
  push_cast at *
  linear_combination 9 * h4 - 24 * h3 + 22 * h2 - 8 * h1 + h0
