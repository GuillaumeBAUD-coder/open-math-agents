import OMAStatements.S_oeis_a054116
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a054116.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 2 := ⟨n - 4, by omega⟩
  rw [show m + 2 + 2 - 1 = m + 2 + 1 by omega, show m + 2 + 2 - 2 = m + 2 by omega]
  simp only [OMA.S_oeis_a054116.a, if_neg (show m + 2 + 2 ≠ 1 by omega),
    if_neg (show m + 2 + 1 ≠ 1 by omega), if_neg (show m + 2 ≠ 1 by omega)]
  rw [show m + 2 + 2 = (m + 2 + 1) + 1 by ring, Finset.sum_Icc_succ_top (by omega),
    Finset.sum_Icc_succ_top (by omega), Nat.factorial_succ (m + 2 + 1), Nat.factorial_succ (m + 2)]
  push_cast
  ring
