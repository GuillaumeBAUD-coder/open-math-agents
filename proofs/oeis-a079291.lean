import OMAStatements.S_oeis_a079291
import Mathlib

open OMA.S_oeis_a079291 in
theorem OMA.solution : type_of% @OMA.S_oeis_a079291.main := by
  have h (n : ℕ) : A (n+1) = A n + 2 * P n ∧ P (n+1) = A n + P n := by
    induction n with
    | zero => simp [A, P]
    | succ n ih =>
      simp [A, P]
      omega
  intro n hn
  have k : ((A n ^ 2 : ℕ) : ℤ) - 2 * (P n ^ 2 : ℕ) = (-1) ^ n := by
    clear hn
    induction n with
    | zero => simp [A, P]
    | succ n ih =>
      rw [(h n).1, (h n).2, pow_succ]
      push_cast at ih ⊢
      linear_combination -ih
  constructor <;> intro e <;> use n <;> rw [e.neg_one_pow] at k <;> omega
