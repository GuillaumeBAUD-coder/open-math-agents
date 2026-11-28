import OMAStatements.S_oeis_a191821

open OMA.S_oeis_a191821 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a191821.main := by
  rw [show (1 - 3*X + 2*X^2 : ℚ⟦X⟧)^3 = 1 - 9*X + 33*X^2 - 63*X^3 + 66*X^4 - 36*X^5 + 8*X^6 by ring]
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | n <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, a,
    ← map_ofNat (C : ℚ →+* ℚ⟦X⟧)] <;> ring
