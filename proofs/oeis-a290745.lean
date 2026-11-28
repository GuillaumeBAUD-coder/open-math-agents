import OMAStatements.S_oeis_a290745
import Mathlib

open OMA.S_oeis_a290745 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a290745.main := by
  rw [show ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2 - X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)
    : ℚ⟦X⟧) = 1 - 2*X + X^2 - X^10 + 2*X^11 - X^12 by ring]
  ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
    ← map_ofNat (C : ℚ →+* _)] <;>
  first
  | (obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 10 ∧ n = 10*q+r := ⟨n/10, n%10, by omega⟩
     interval_cases r <;>
     simp only [b, a, add_assoc, Nat.reduceAdd, show ∀ c, (10*q+c)/10 = q+c/10 by omega,
       show ∀ c, (10*q+c)%10 = c%10 by omega, show ∀ c, ¬ 10*q+(c+1) = 0 by omega, if_false,
       Nat.reduceMod, Nat.reduceDiv] <;>
     push_cast [Nat.cast_choose_two] <;> ring)
  | norm_num [b, a, Nat.choose]
