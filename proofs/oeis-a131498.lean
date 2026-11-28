import OMAStatements.S_oeis_a131498
import Mathlib

open OMA.S_oeis_a131498 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a131498.main := by
  have d (m : ℕ) : 2*(m+1)*(2*(m+1)-1)/2 = (m+1)*(2*m+1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ two_pos, mul_add 2 m 1]
    rfl
  have h (n : ℕ) : (a (n+13) : ℤ) = 3*a (n+9) - 3*a (n+5) + a (n+1) := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4*q+r := ⟨n/4, n%4, by omega⟩
    interval_cases r <;>
    simp [a, quad, d, add_assoc, show ∀ c, (4*q+c)/4 = q+c/4 by omega,
      show ∀ c, (4*q+c)%4 = c%4 by omega] <;> ring
  rw [show ((1 - X)^3*(1+X)^3*(1+X^2)^3 : ℤ⟦X⟧) = 1 - 3*X^4 + 3*X^8 - X^12 by ring]
  ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
  simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
    ← map_ofNat (C : ℤ →+* _), -eq_intCast] <;>
  first | linarith [h n] | simp [a, quad]
