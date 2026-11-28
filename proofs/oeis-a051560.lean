import OMAStatements.S_oeis_a051560
import Mathlib
open OMA.S_oeis_a051560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a051560.main := by
  have h (n : ℕ) : a n = (-1) ^ (n + 1) * T n 1 := by
    have key (n : ℕ) : 0 ≤ (-1) ^ n * T n 0 ∧ 0 ≤ (-1) ^ (n + 1) * T n 1 := by
      induction n with
      | zero => simp [T]
      | succ n ih =>
        simp only [T, pow_succ] at ih ⊢
        push_cast
        have c : (0 : ℤ) ≤ n + 1 + 7 := by positivity
        constructor <;> nlinarith [mul_nonneg c ih.1, mul_nonneg c ih.2]
    rw [a, ← abs_of_nonneg (key n).2, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  intro n
  simp only [h, T, pow_succ]
  push_cast
  ring
