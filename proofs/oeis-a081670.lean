import OMAStatements.S_oeis_a081670
import Mathlib

open OMA.S_oeis_a081670 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  have h (k : ℕ) : ((k : ℤ) + 1) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, a]
  have h2 := h (m + 2)
  have h1 := h (m + 1)
  have h0 := h m
  push_cast at h0 h1 h2 ⊢
  linear_combination (3 * (m : ℤ) ^ 2 + m + 2) * h2 - (12 * (m : ℤ) ^ 2 + 16 * m + 8) * h1 +
    (9 * (m : ℤ) ^ 2 + 21 * m + 18) * h0
