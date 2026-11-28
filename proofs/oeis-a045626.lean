import OMAStatements.S_oeis_a045626

open OMA.S_oeis_a045626 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a045626.main := by
  ext (_ | _ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, sub_mul, mul_add, add_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, a,
    ← map_ofNat (C : ℚ →+* _)] <;> ring
