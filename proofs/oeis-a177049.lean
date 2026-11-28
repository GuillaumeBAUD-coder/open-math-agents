import OMAStatements.S_oeis_a177049
import Mathlib

open OMA.S_oeis_a177049 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a177049.main := by
  have v0 (q : ℕ) : a (4*q) = (12*q+1)*(6*q+1) := by
    have : ((3*((4*q:ℕ):ℚ)+1)*(3*((4*q:ℕ):ℚ)+2)/4) = (((12*q+1)*(6*q+1) : ℤ) : ℚ) / ((2:ℤ):ℚ) := by
      push_cast
      ring
    rw [a, this, Rat.num_div_eq_of_coprime two_pos
      (Nat.coprime_two_right.2 (Int.natAbs_odd.2 (Odd.mul ⟨6*q, by ring⟩ ⟨3*q, by ring⟩)))]
  have v1 (q : ℕ) : a (4*q+1) = (3*q+1)*(12*q+5) := by
    have : ((3*((4*q+1:ℕ):ℚ)+1)*(3*((4*q+1:ℕ):ℚ)+2)/4) = (((3*q+1)*(12*q+5) : ℤ) : ℚ) := by
      push_cast
      ring
    rw [a, this, Rat.num_intCast]
  have v2 (q : ℕ) : a (4*q+2) = (12*q+7)*(3*q+2) := by
    have : ((3*((4*q+2:ℕ):ℚ)+1)*(3*((4*q+2:ℕ):ℚ)+2)/4) = (((12*q+7)*(3*q+2) : ℤ) : ℚ) := by
      push_cast
      ring
    rw [a, this, Rat.num_intCast]
  have v3 (q : ℕ) : a (4*q+3) = (6*q+5)*(12*q+11) := by
    have : ((3*((4*q+3:ℕ):ℚ)+1)*(3*((4*q+3:ℕ):ℚ)+2)/4) = (((6*q+5)*(12*q+11) : ℤ) : ℚ) / ((2:ℤ):ℚ) := by
      push_cast
      ring
    rw [a, this, Rat.num_div_eq_of_coprime two_pos
      (Nat.coprime_two_right.2 (Int.natAbs_odd.2 (Odd.mul ⟨3*q+2, by ring⟩ ⟨6*q+5, by ring⟩)))]
  have h (n : ℕ) : a (n+9) = 3*a (n+8) - 6*a (n+7) + 10*a (n+6) - 12*a (n+5) + 12*a (n+4) -
      10*a (n+3) + 6*a (n+2) - 3*a (n+1) + a n := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4*q+r := ⟨n/4, n%4, by omega⟩
    have e0 := v0 q
    have e1 := v1 q
    have e2 := v2 q
    have e3 := v3 q
    have e4 := v0 (q+1)
    have e5 := v1 (q+1)
    have e6 := v2 (q+1)
    have e7 := v3 (q+1)
    have e8 := v0 (q+2)
    have e9 := v1 (q+2)
    have e10 := v2 (q+2)
    have e11 := v3 (q+2)
    have e12 := v0 (q+3)
    interval_cases r <;> simp [mul_add, add_assoc] at * <;> linarith
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h k
  · rw [denominator, generating, numerator, mul_comm,
      show ((1 - X)^3*(X^2+1)^3 : ℤ⟦X⟧) = 1 - 3*X + 6*X^2 - 10*X^3 + 12*X^4 - 12*X^5 + 10*X^6
        - 6*X^7 + 3*X^8 - X^9 by ring]
    have s : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 14 ∧ a 3 = 55 ∧ a 4 = 91 ∧ a 5 = 68 ∧ a 6 = 95 ∧
        a 7 = 253 ∧ a 8 = 325 := by
      first | decide | norm_num [a]
    ext (_ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, mul_add, sub_mul, add_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X,
      coeff_C, coeff_mul_C, ← map_ofNat (C : ℤ →+* _), -eq_intCast] <;>
    first | linarith [h n] | simp [s]
