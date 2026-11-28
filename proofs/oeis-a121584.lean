import OMAStatements.S_oeis_a121584
import Mathlib

open OMA.S_oeis_a121584 in
set_option maxRecDepth 8000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121584.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [a, add_assoc, Nat.factorial_succ]
  ring_nf
  field_simp
  ring
