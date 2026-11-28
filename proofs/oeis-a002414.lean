import OMAStatements.S_oeis_a002414

open OMA.S_oeis_a002414 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a002414.main := by
  ext (_ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, sub_mul, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, a,
    ← map_ofNat (C : ℚ →+* _)] <;> ring
