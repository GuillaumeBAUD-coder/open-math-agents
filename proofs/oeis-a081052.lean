import OMAStatements.S_oeis_a081052
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A081052 (statement by @ivillar).
-- Idea: with D f(n) = f(n+1) + n*f(n), the signed Stirling numbers satisfy D s(.,k+1) = s(.,k)
-- (the triangle recurrence s(n+1,k+1) = s(n,k) - n*s(n,k+1)), and D s(.,0) = 0 away from n = 0.
-- For f(n) = s(n,2) - s(n,3), so that a(n) = f(n+1), D^3 f(n) = -s(n,0) vanishes for n ≥ 1, and
-- D^3 f(n) = f(n+3) + 3(n+1) f(n+2) + (3n^2+3n+1) f(n+1) + n^3 f(n) is the conjectured recurrence.
-- Unfolding the triangle recurrence down to row n-2 makes the claim a polynomial identity.

namespace OMAA081052Helpers

open OMA.S_oeis_a081052

theorem s_succ_succ (n k : ℕ) : s (n + 1) (k + 1) = s n k - n * s n (k + 1) := by
  unfold s
  rw [Nat.stirlingFirst_succ_succ]
  push_cast
  ring

theorem s_succ_zero (n : ℕ) : s (n + 1) 0 = 0 := by
  simp [s, Nat.stirlingFirst_succ_zero]

end OMAA081052Helpers

open OMA.S_oeis_a081052 OMAA081052Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a081052.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [a, s_succ_succ, s_succ_zero]
  push_cast
  ring
