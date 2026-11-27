import OMAStatements.S_oeis_a185020
import Mathlib

-- Problem: oeis-a185020
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P185020
open OMA.S_oeis_a185020

lemma cat_rec (n : ℕ) : ((n + 2 : ℕ) : ℤ) * (catalan (n + 1) : ℤ) = 2 * (2 * (n : ℤ) + 1) * (catalan n : ℤ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 := succ_mul_catalan_eq_centralBinom n
  have h3 := Nat.succ_mul_centralBinom_succ n
  have : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (2 * (2 * n + 1) * catalan n) := by
    calc (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * Nat.centralBinom (n + 1) := by
          rw [← h1]
      _ = 2 * (2 * n + 1) * Nat.centralBinom n := h3
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by rw [← h2]; ring
  have := Nat.eq_of_mul_eq_mul_left (by omega) this
  exact_mod_cast this

theorem sol : type_of% @OMA.S_oeis_a185020.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show m + 2 + 1 = (m + 1) + 2 by ring, s]
  have c1 := cat_rec (m + 1)
  have c0 := cat_rec m
  push_cast at c1 c0 ⊢
  rw [show m + 1 + 1 = m + 2 by ring] at c1
  linear_combination (2 * ((m : ℤ) + 2)) * (s (m + 2) + s (m + 1)) * c1 +
    (4 * (2 * (m : ℤ) + 3)) * s (m + 1) * c0

theorem OMA.solution : type_of% @OMA.S_oeis_a185020.main := OMA.P185020.sol
