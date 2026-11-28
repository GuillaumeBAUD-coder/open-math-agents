import OMAStatements.S_oeis_a159715
import Mathlib

open OMA.S_oeis_a159715 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a159715.main := by
  refine ⟨?_, fun n hn => ?_, fun n hn => ?_⟩
  · rw [show (1 - 3 * X : ℚ⟦X⟧) ^ 2 = 1 - C 6 * X + C 9 * X ^ 2 by simp only [map_ofNat]; ring, show (2 * X ^ 2 * (2 - 3 * X) : ℚ⟦X⟧) = C 4 * X ^ 2 - C 6 * X ^ 3 by simp only [map_ofNat]; ring]
    ext (_ | _ | _ | _ | n) <;> simp [mul_add, mul_sub, coeff_mul_X_pow', a, mul_left_comm _ (C _)] <;> ring_nf
  · rw [a, if_neg (by omega)]
    ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [a, pow_succ]
    ring
