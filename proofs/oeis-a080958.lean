import OMAStatements.S_oeis_a080958
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A080958 (statement by @ivillar).
-- Idea: a(n+1) = (n+1)*a(n) + (-1)^n*(n+2)*n!; eliminating the (-1)^n*n! terms between two
-- consecutive instances of this step gives the recurrence.

namespace OMAA080958Helpers

open OMA.S_oeis_a080958

theorem step (n : ℕ) :
    a (n + 1) = ((n : ℚ) + 1) * a n + (-1 : ℚ) ^ n * ((n : ℚ) + 2) * n.factorial := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.factorial_succ]
  push_cast
  have h : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

end OMAA080958Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a080958.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega]
  have h1 := OMAA080958Helpers.step (m + 1)
  have h0 := OMAA080958Helpers.step m
  rw [Nat.factorial_succ] at h1
  push_cast at h1 h0 ⊢
  linear_combination (-((m : ℚ) + 2)) * h1 + (-((m : ℚ) + 1) * ((m : ℚ) + 3)) * h0
