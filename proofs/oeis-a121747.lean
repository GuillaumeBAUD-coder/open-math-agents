import OMAStatements.S_oeis_a121747
import Mathlib

open OMA.S_oeis_a121747 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121747.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have p : ∀ i c, (2*i+c)/2 = i + c/2 := by omega
  have q : ∀ i c, (2*i+c)%2 = c%2 := by omega
  obtain ⟨i, rfl | rfl⟩ := k.even_or_odd'
  · rcases i with _ | i <;> simp [a, d, Nat.factorial_succ, mul_add, add_assoc, p, q] <;> ring
  · simp [a, d, Nat.factorial_succ, mul_add, add_assoc, p, q]
    ring
