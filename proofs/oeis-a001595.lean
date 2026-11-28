import OMAStatements.S_oeis_a001595
import Mathlib

open PowerSeries OMA.S_oeis_a001595 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001595.main := by
  refine ⟨?_, ?_⟩ <;>
  (ring_nf; ext n; rcases n with _ | _ | _ | _ | n <;> simp [coeff_mul_X_pow', coeff_X_pow_mul', coeff_succ_X_mul, coeff_C_mul, coeff_X_pow, coeff_X, ← map_ofNat C, -eq_intCast, coeff_mul_C, coeff_succ_mul_X, a] <;> ring)
