import OMAStatements.S_oeis_a003435
import Mathlib

open OMA.S_oeis_a003435 in
theorem OMA.solution : type_of% @OMA.S_oeis_a003435.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [a, add_assoc]
  ring_nf
  field_simp
  ring
