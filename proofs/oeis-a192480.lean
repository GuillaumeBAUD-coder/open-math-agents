import OMAStatements.S_oeis_a192480
import Mathlib

open OMA.S_oeis_a192480 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192480.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have r1 := r (k+1)
  have r2 := r (k+2)
  simp [a, add_assoc] at r1 r2 ⊢
  linear_combination (3*k*k+8*k+3)*r2 - (3*k*k+14*k+14)*r1
