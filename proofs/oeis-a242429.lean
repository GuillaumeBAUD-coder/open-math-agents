import OMAStatements.S_oeis_a242429
import Mathlib

open OMA.S_oeis_a242429 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242429.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (j : ℕ) : 2 * (((2*(j+1)).choose (j+1) / 2 : ℕ) : ℤ) = (j+1).centralBinom :=
    mod_cast Nat.mul_div_cancel' (Nat.two_dvd_centralBinom_succ j)
  have r (j : ℕ) : ((j:ℤ)+2) * (((2*(j+1+1)).choose (j+1+1) / 2 : ℕ) : ℤ)
      = 2*(2*j+3) * (((2*(j+1)).choose (j+1) / 2 : ℕ) : ℤ) := by
    have h := (j+1).succ_mul_centralBinom_succ
    zify at h
    exact mul_left_cancel₀ two_ne_zero (by linear_combination (j+2:ℤ) * e (j+1) + h - 2*(2*j+3) * e j)
  have r4 := r (k+3)
  have r3 := r (k+2)
  have r2 := r (k+1)
  have r1 := r k
  simp [a, add_assoc] at r1 r2 r3 r4 ⊢
  linear_combination (131*(k+5:ℤ)-376) * r4 + 2*(-301*(k+5:ℤ)+809) * r3
    + (889*(k+5:ℤ)-2172) * r2 + 2*(-209*(k+5:ℤ)+387) * r1
