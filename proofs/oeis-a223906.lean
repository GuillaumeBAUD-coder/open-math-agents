import OMAStatements.S_oeis_a223906
import Mathlib

open OMA.S_oeis_a223906 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a223906.main := by
  have h (n : ℕ) : a n = 2*2^n + 3*3^n + 4^n := by
    simp [a, hatC, Finset.sum_range_succ, Nat.stirlingFirst]
    ring
  constructor
  · intro n _
    rw [h]
    ring
  · rw [eq_mul_inv_iff_mul_eq (by simp)]
    ext (_ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C, h,
      ← map_ofNat (C : ℚ →+* _)] <;> ring
