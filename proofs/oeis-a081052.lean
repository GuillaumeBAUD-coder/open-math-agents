import OMAStatements.S_oeis_a081052
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a081052.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp [OMA.S_oeis_a081052.a, OMA.S_oeis_a081052.s, Nat.stirlingFirst_succ_succ]
  ring
