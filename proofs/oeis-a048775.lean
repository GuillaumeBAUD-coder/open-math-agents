import OMAStatements.S_oeis_a048775
import Mathlib

open OMA.S_oeis_a048775 in
theorem OMA.solution : type_of% @OMA.S_oeis_a048775.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (j : ℕ) : 2 * ((2*j+1).choose (j+1) : ℤ) = (j+1).centralBinom := by
    rw [Nat.centralBinom, show 2*(j+1) = 2*j+1+1 from rfl, Nat.choose_succ_succ' (2*j+1), Nat.choose_symm_half]
    push_cast
    ring
  have r (j : ℕ) : ((j:ℤ)+2) * (2*(j+1)+1).choose (j+1+1) = 2*(2*j+3) * (2*j+1).choose (j+1) := by
    have h := (j+1).succ_mul_centralBinom_succ
    zify at h
    exact mul_left_cancel₀ two_ne_zero (by linear_combination (j+2:ℤ) * e (j+1) + h - 2*(2*j+3) * e j)
  have r4 := r (k+4)
  have r3 := r (k+3)
  have r2 := r (k+2)
  have r1 := r (k+1)
  simp [a, mul_add, add_assoc] at r1 r2 r3 r4 ⊢
  linear_combination r4 - 3 * r3 + 3 * r2 - r1
