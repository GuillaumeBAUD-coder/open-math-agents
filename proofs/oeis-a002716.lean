import OMAStatements.S_oeis_a002716
import Mathlib

namespace A002716

open OMA.S_oeis_a002716 in
lemma even_step (k : ℕ) : a (2 * k + 2) = a (2 * k + 1) ^ 2 - 3 * a (2 * k + 1) + 3 := by
  rw [a, if_pos (by omega)]

open OMA.S_oeis_a002716 in
lemma odd_step (k : ℕ) : a (2 * k + 1 + 2) = a (2 * k + 2) + a (2 * k + 1) - 1 := by
  rw [a, if_neg (by omega)]

end A002716

theorem OMA.solution : type_of% @OMA.S_oeis_a002716.main := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a002716.a]
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [e, A002716.odd_step, A002716.even_step, ih]
    have : (2 : ℤ) ^ (2 ^ (k + 1 + 1)) = (2 ^ (2 ^ (k + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (k + 1)]
    rw [this]; ring
