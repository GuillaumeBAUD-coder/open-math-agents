import OMAStatements.S_oeis_a400217
import Mathlib

open OMA.S_oeis_a400217 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a400217.main := by
  have h (m : ℕ) : a (m+3) = 3^m * v (m+3) 1 := by
    rcases m with _ | m <;> simp [a]
  simp only [← map_ofNat (C (R := ℚ))]
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first
  | (simp [mul_add, mul_sub, add_mul, sub_mul, ← mul_assoc, pow_succ, h, v, coeff_X, coeff_one]
     ring; done)
  | (simp [mul_add, mul_sub, add_mul, sub_mul, ← mul_assoc, pow_succ, a, v, coeff_X, coeff_one]
     try norm_num)
