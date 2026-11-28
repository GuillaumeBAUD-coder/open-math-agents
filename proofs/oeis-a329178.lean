import OMAStatements.S_oeis_a329178
import Mathlib

open OMA.S_oeis_a329178 PowerSeries Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a329178.main := by
  have h (n : ℕ) : a (n+7) = 2*a (n+6) - 2*a (n+3) + 2*a (n+2) - 2*a (n+1) + a n := by
    simp [a, sum_range_succ, padovan]
    ring
  constructor
  · intro x
    rw [mul_comm]
    ext (_ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [x, pow_succ, mul_sub, sub_mul, mul_add, add_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X,
      ← map_ofNat (C : ℤ →+* _), coeff_mul_C, -eq_intCast] <;>
    first | linarith [h n] | simp [a, sum_range_succ, padovan]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact h k
