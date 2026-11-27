import OMAStatements.S_oeis_a171556
import Mathlib

-- Problem: oeis-a171556
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P171556
open OMA.S_oeis_a171556

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

lemma cat_pos (n : ℕ) : 1 ≤ catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have h2 := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0] at h; omega
  · exact h0

theorem sol : type_of% @OMA.S_oeis_a171556.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  unfold a
  have p0 := cat_pos m
  have p1 := cat_pos (m + 1)
  have p2 := cat_pos (m + 2)
  have c1 := cat_rec (m + 1)
  have c0 := cat_rec m
  rw [show m + 1 + 1 = m + 2 by ring] at c1
  push_cast [Nat.cast_sub (show 2 ≤ 3 * catalan m by omega), Nat.cast_sub (show 2 ≤ 3 * catalan (m + 1) by omega),
    Nat.cast_sub (show 2 ≤ 3 * catalan (m + 2) by omega)] at c1 c0 ⊢
  linear_combination 3 * (m : ℤ) * c1 - 3 * ((m : ℤ) + 1) * c0

theorem OMA.solution : type_of% @OMA.S_oeis_a171556.main := OMA.P171556.sol
