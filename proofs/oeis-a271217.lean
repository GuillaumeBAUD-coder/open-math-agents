import OMAStatements.S_oeis_a271217
import Mathlib

open OMA.S_oeis_a271217 in
theorem OMA.solution : type_of% @OMA.S_oeis_a271217.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k <;> rcases i with _ | j <;> first
  | (norm_num [a]; done)
  | (simp [a, mul_add, add_assoc, show ∀ c, (2*j+c)%2 = c%2 by omega]; ring)
