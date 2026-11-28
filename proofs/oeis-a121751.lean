import OMAStatements.S_oeis_a121751
import Mathlib

open OMA.S_oeis_a121751 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121751.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;>
  simp [a, add_assoc, show ∀ c, (2*i+c)/2 = i+c/2 by omega] <;> ring
