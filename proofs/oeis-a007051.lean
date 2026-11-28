import OMAStatements.S_oeis_a007051
import Mathlib

open OMA.S_oeis_a007051 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007051.main := by
  intro s h1 h n hn
  have H : s n * (3^n - 1) = 3^n + 1 := by
    induction n, hn using Nat.le_induction with
    | base =>
      rw [h1]
      norm_num
    | succ m hm ih =>
      have t : (1:ℚ) < 3^m := one_lt_pow₀ (by norm_num) (by omega)
      rw [h _ (by omega), Nat.add_sub_cancel, div_mul_eq_mul_div, div_eq_iff (fun q => by
        rw [show s m = -2 by linarith] at ih
        linarith), pow_succ]
      linear_combination 3*ih
  have t : (1:ℚ) < 3^n := one_lt_pow₀ (by norm_num) (by omega)
  rw [show (a n : ℚ) = (3^n+1)/2 by
    rw [a, Nat.cast_div (Odd.pow (by decide : Odd 3) : Odd (3^n)).add_one.two_dvd two_ne_zero]
    norm_num, eq_div_iff (ne_of_gt (by linarith))]
  linear_combination H/2
