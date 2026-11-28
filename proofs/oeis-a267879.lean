import OMAStatements.S_oeis_a267879
import Mathlib

namespace OMA.S_oeis_a267879

open PowerSeries

theorem state_one : state 233 1 = fun x => decide (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 by omega)]
    decide

theorem state_two : state 233 2 = fun x => decide (x ≠ -1 ∧ x ≠ 1) := by
  funext x
  rw [show state 233 2 = step 233 (state 233 1) from rfl, state_one]
  simp only [step]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega)
    with h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 0 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 0 ∧ x + 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 0 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 0 ∧ x + 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega)]
    decide

theorem state_three : state 233 3 = fun x => decide (x ≠ 0) := by
  funext x
  rw [show state 233 3 = step 233 (state 233 2) from rfl, state_two]
  simp only [step]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega)
    with h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ 0 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ 0 by omega)]
    decide

theorem state_four : state 233 4 = fun _ => true := by
  funext x
  rw [show state 233 4 = step 233 (state 233 3) from rfl, state_three]
  simp only [step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ 0 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ 0 by omega)]
    decide

theorem state_ge (n : ℕ) (hn : 4 ≤ n) : state 233 n = fun _ => true := by
  induction n, hn using Nat.le_induction with
  | base => exact state_four
  | succ n hn ih =>
    funext x
    rw [show state 233 (n + 1) = step 233 (state 233 n) from rfl, ih]
    simp only [step, Bool.toNat_true]
    decide

theorem c_ge (n : ℕ) (hn : 4 ≤ n) : c n = 1 := by
  rw [c, state_ge n hn]
  rfl

theorem a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  rw [a, a, Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem a0 : a 0 = 1 := by decide
theorem a1 : a 1 = 10 := by decide
theorem a2 : a 2 = 101 := by decide
theorem a3 : a 3 = 1010 := by decide

theorem a_step (n : ℕ) (hn : 3 ≤ n) : a (n + 1) = 10 * a n + 1 := by
  rw [a_succ, c_ge (n + 1) (by omega)]

theorem a4 : a 4 = 10101 := by rw [a_step 3 le_rfl, a3]

theorem closed (n : ℕ) (hn : 3 ≤ n) : 9 * a n + 1 = 9091 * 10 ^ (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => rw [a3]; norm_num
  | succ n hn ih =>
    rw [a_step n hn, show n + 1 - 3 = (n - 3) + 1 by omega, pow_succ]
    linarith

theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega]
  have h1 : a (k + 5) = 10 * a (k + 4) + 1 := a_step (k + 4) (by omega)
  have h2 : a (k + 4) = 10 * a (k + 3) + 1 := a_step (k + 3) (by omega)
  rw [h1, h2]
  push_cast
  ring

theorem gf_mul : A * ((1 - X) * (1 - 10 * X)) = 1 - X + X ^ 2 - X ^ 3 + X ^ 4 := by
  have hD : A * ((1 - X) * (1 - 10 * X)) = A - C 11 * (A * X ^ 1) + C 10 * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - X + X ^ 2 - X ^ 3 + X ^ 4 : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 1 * X ^ 1 + C 1 * X ^ 2 - C 1 * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_one]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2, a3, a4]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 11 * a (m - 1) - 10 * a (m - 2) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    have k4 : m - 4 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, Nat.zero_le, k0, k1, k2, k3, k4, coeff_C, if_true, if_false, hq]
    ring

end OMA.S_oeis_a267879

theorem OMA.solution : type_of% @OMA.S_oeis_a267879.main := by
  refine ⟨OMA.S_oeis_a267879.recurrence, ?_, fun n hn => ?_⟩
  · have h0 : PowerSeries.constantCoeff
        ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
    rw [← OMA.S_oeis_a267879.gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]
  · have h := OMA.S_oeis_a267879.closed n (by omega)
    have hq : (9 : ℚ) * OMA.S_oeis_a267879.a n + 1 = 9091 * 10 ^ (n - 3) := by exact_mod_cast h
    linarith
