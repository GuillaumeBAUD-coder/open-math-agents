import OMAStatements.S_oeis_a082143
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a082143.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [OMA.S_oeis_a082143.a, OMA.S_oeis_a082143.T, show m + 2 - 1 = m + 1 by omega,
    show m + 2 + (m + 2 + 1) = 2 * m + 3 + 2 by ring, show m + 1 + (m + 1 + 1) = 2 * m + 3 by ring,
    Nat.cast_choose ℚ (show m + 2 ≤ 2 * m + 3 + 2 by omega),
    Nat.cast_choose ℚ (show m + 1 ≤ 2 * m + 3 by omega),
    show 2 * m + 3 + 2 - (m + 2) = m + 2 + 1 by omega, show 2 * m + 3 - (m + 1) = m + 1 + 1 by omega,
    show (((m + 2 : ℕ) : ℤ) - 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
    show (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    Nat.factorial_succ, zero_pow (Nat.succ_ne_zero _)]
  push_cast
  field_simp
  ring
