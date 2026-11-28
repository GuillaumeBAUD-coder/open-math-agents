import OMAStatements.S_oeis_a223173
import Mathlib

open OMA.S_oeis_a223173 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a223173.main := by
  have h (n : ℕ) : a n = 2*2^n - 3*3^n + 4^n := by
    simp [a, stirling1, Finset.sum_range_succ, Nat.stirlingFirst]
    ring
  constructor
  · intro n _
    rw [h]
    ring
  · rw [show (fun n => if n = 0 then 0 else a n) = a by ext n; cases n <;> simp [h]]
    ext (_ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C, h,
      ← map_ofNat (C : ℤ →+* _), -eq_intCast] <;> ring
