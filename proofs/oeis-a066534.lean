import OMAStatements.S_oeis_a066534
import Mathlib

open OMA.S_oeis_a066534 in
theorem OMA.solution : type_of% @OMA.S_oeis_a066534.main := by
  have s (j : ℕ) : a (j+1) = (j+1)*a j + (j+1)*2^j := by
    rw [a, a, Finset.sum_range_succ, Finset.mul_sum, Nat.factorial_succ,
      Nat.mul_div_cancel _ j.factorial_pos]
    congr 1
    exact Finset.sum_congr rfl fun x hx => by
      rw [Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Finset.mem_range.1 hx).le), mul_assoc]
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [s]
  ring
