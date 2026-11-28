import OMAStatements.S_oeis_a296516
import Mathlib

open OMA.S_oeis_a296516 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a296516.main := by
  have c (n m : ℕ) : ((Nat.fib (2*n+(m+4)) : ℕ) : ℚ) =
      3*Nat.fib (2*n+(m+2)) - Nat.fib (2*n+m) := by
    simp only [← add_assoc, Nat.fib_add_two]
    push_cast
    ring
  have d (n m : ℕ) : ((Nat.fib (n+(m+2)) : ℕ) : ℚ) = Nat.fib (n+(m+1)) + Nat.fib (n+m) := by
    simp only [← add_assoc, Nat.fib_add_two]
    push_cast
    ring
  constructor
  · rw [show ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) : ℚ⟦X⟧) =
      X^7-5*X^6+6*X^5+6*X^4-20*X^3+18*X^2-7*X+1 by ring]
    ext (_ | _ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, mul_add, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_mul_C,
      ← map_ofNat (C : ℚ →+* _), a, add_assoc, c, d] <;> ring
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [a, mul_add, add_assoc, c, d]
    ring
