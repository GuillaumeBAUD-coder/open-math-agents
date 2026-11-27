import OMAStatements.S_oeis_a014137
import Mathlib

-- Problem: oeis-a014137
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P014137
open OMA.S_oeis_a014137

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

lemma catq (n : ℕ) : (catalan (n + 1) : ℚ) = 2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ) / ((n : ℚ) + 2) := by
  have h := cat_rec n
  rw [eq_div_iff (by positivity)]
  have h' : ((((n + 2 : ℕ) : ℤ) * (catalan (n + 1) : ℤ) : ℤ) : ℚ) = ((2 * (2 * (n : ℤ) + 1) * (catalan n : ℤ) : ℤ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination h'

theorem sol : type_of% @OMA.S_oeis_a014137.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← Int.cast_inj (α := ℚ)]
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  unfold a
  rw [show m + 2 + 1 = (m + 1 + 1) + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ (n := m + 1)]
  push_cast
  rw [show m + 1 + 1 = (m + 1) + 1 by ring, catq (m + 1)]
  push_cast
  field_simp
  ring

end OMA.P014137

theorem OMA.solution : type_of% @OMA.S_oeis_a014137.main := OMA.P014137.sol
