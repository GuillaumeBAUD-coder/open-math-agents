import OMAStatements.S_oeis_a324036
import Mathlib

open OMA.S_oeis_a324036

theorem OMA.solution : type_of% @OMA.S_oeis_a324036.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
  unfold a
  split_ifs <;> omega
