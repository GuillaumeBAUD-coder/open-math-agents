import OMAStatements.S_oeis_a348618
import Mathlib

open OMA.S_oeis_a348618 in
theorem OMA.solution : type_of% @OMA.S_oeis_a348618.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · simp (disch := omega) [a, add_assoc, pow_add, pow_mul, Nat.cast_choose ℚ, Nat.factorial_succ,
      show 3*(2*i+3)-1 = 6*i+8 by omega, show (6*i+8)/2 = 3*i+4 by omega,
      show 3*(2*i+1)-1 = 6*i+2 by omega, show (6*i+2)/2 = 3*i+1 by omega,
      show (2*i+2)/2 = i+1 by omega, show 3*i+4-(2*i+3) = i+1 by omega,
      show 6*i+8-(3*i+4) = 3*i+4 by omega, show 2*i+2-(i+1) = i+1 by omega,
      show 3*i+1-(2*i+1) = i by omega, show 6*i+2-(3*i+1) = 3*i+1 by omega,
      show 2*i-i = i by omega]
    field_simp
    ring
  · simp (disch := omega) [a, add_assoc, pow_add, pow_mul, Nat.cast_choose ℚ, Nat.factorial_succ,
      show 3*(2*i+4)/2-1 = 3*i+5 by omega, show 3*(2*i+2)/2-1 = 3*i+2 by omega,
      show 3*i+5-(2*i+4) = i+1 by omega, show 3*i+2-(2*i+2) = i by omega]
    field_simp
    ring
