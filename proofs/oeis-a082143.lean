import OMAStatements.S_oeis_a082143
import Mathlib

/-!
For `n = m + 2` the terms are `2^(m+1) C(2m+5, m+2)` and `2^m C(2m+3, m+1)`
(the `0^n/2` correction vanishes). Writing both binomials with factorials, the
recurrence `(n+1) a(n) = 4 (2n+1) a(n-1)` is a rational-function identity.
-/

open OMA.S_oeis_a082143

theorem OMA.solution : type_of% @OMA.S_oeis_a082143.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  simp only [a, T]
  have h1 : (m + 2 + (m + 2 + 1)) = 2 * m + 5 := by ring
  have h2 : (m + 1 + (m + 1 + 1)) = 2 * m + 3 := by ring
  rw [h1, h2]
  rw [Nat.cast_choose ℚ (by omega : m + 2 ≤ 2 * m + 5),
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 2 * m + 3)]
  have h3 : 2 * m + 5 - (m + 2) = m + 3 := by omega
  have h4 : 2 * m + 3 - (m + 1) = m + 2 := by omega
  rw [h3, h4]
  have z1 : (0:ℚ) ^ (m + 2) = 0 := by simp
  have z2 : (0:ℚ) ^ (m + 1) = 0 := by simp
  rw [z1, z2]
  have p1 : (2:ℚ) ^ (((m + 2 : ℕ) : ℤ) - 1) = 2 * 2 ^ m := by
    rw [show (((m + 2 : ℕ) : ℤ) - 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    ring
  have p2 : (2:ℚ) ^ (((m + 1 : ℕ) : ℤ) - 1) = 2 ^ m := by
    rw [show (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [p1, p2]
  rw [show 2 * m + 5 = (2 * m + 3) + 2 by ring, Nat.factorial_succ, Nat.factorial_succ,
    show m + 3 = (m + 2) + 1 by ring, Nat.factorial_succ (m + 2)]
  rw [show m + 2 = (m + 1) + 1 by ring, Nat.factorial_succ (m + 1)]
  push_cast
  field_simp
  ring
