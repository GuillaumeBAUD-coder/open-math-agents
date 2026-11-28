import OMAStatements.S_oeis_a383702
import Mathlib

open OMA.S_oeis_a383702 Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a383702.main := by
  have r (m k : ℕ) : (row (m+1)).coeff (k+1) = (row m).coeff k + (4*m+3) * (row m).coeff (k+1) := by
    rw [row, Finset.prod_range_succ, ← row, mul_add, coeff_add, coeff_mul_X, coeff_mul_C]
    ring
  have r0 (m : ℕ) : (row (m+1)).coeff 0 = (4*m+3) * (row m).coeff 0 := by
    rw [row, Finset.prod_range_succ, ← row, mul_add, coeff_add, coeff_mul_X_zero, coeff_mul_C]
    ring
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [a, r, r0]
  ring
