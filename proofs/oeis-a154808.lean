import OMAStatements.S_oeis_a154808
import Mathlib

open OMA.S_oeis_a154808 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a154808.main := by
  have z : a 5 0 = 0 := by simp [a, digits]
  have st (n : ℕ) : a 5 (n+1) = 32 * a 5 n + if n % 2 = 0 then 31 else 0 := by
    rw [a, digits, Nat.ofDigits_append]
    split_ifs <;> simp [a, Nat.ofDigits, List.replicate] <;> ring
  have c (n : ℕ) : 66*a 5 n = 2^(6+5*n)-31*(-1)^n-33 := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      rw [neg_one_pow_eq_pow_mod_two] at ih
      rw [st, pow_succ, neg_one_pow_eq_pow_mod_two (n := n)]
      rcases n.mod_two_eq_zero_or_one with e | e <;> simp [e, mul_add, pow_add] at ih ⊢ <;> linarith
  refine ⟨fun n _ => c n, ?_⟩
  rw [mul_comm]
  ext (_ | _ | _ | n) <;>
    simp [pow_succ, mul_sub, sub_mul, ← mul_assoc, coeff_succ_mul_X, coeff_X, coeff_C, coeff_mul_C,
      -eq_intCast, st, z] <;> (try split_ifs) <;> omega
