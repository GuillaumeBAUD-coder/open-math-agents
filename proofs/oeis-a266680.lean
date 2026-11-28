import OMAStatements.S_oeis_a266680
import Mathlib

namespace OMA.S_oeis_a266680

open PowerSeries

theorem state_one : state 175 1 = fun x => decide (x ≠ 1) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide

theorem state_succ (n : ℕ) (k : ℤ) (h : state 175 n = fun x => decide (x ≠ k)) :
    state 175 (n + 1) = fun x => decide (x ≠ k - 1) := by
  funext x
  rw [show state 175 (n + 1) = step 175 (state 175 n) from rfl, h]
  simp only [step]
  rcases (show x ≤ k - 3 ∨ x = k - 2 ∨ x = k - 1 ∨ x = k ∨ k + 1 ≤ x by omega)
    with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_true (show x + 1 ≠ k by omega), decide_eq_true (show x ≠ k - 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_true (show x + 1 ≠ k by omega), decide_eq_true (show x ≠ k - 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_false (show ¬ (x + 1 ≠ k) by omega), decide_eq_false (show ¬ (x ≠ k - 1) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_false (show ¬ (x ≠ k) by omega),
      decide_eq_true (show x + 1 ≠ k by omega), decide_eq_true (show x ≠ k - 1 by omega)]
    decide
  · rcases (show x = k + 1 ∨ k + 2 ≤ x by omega) with h' | h'
    · rw [decide_eq_false (show ¬ (x - 1 ≠ k) by omega), decide_eq_true (show x ≠ k by omega),
        decide_eq_true (show x + 1 ≠ k by omega), decide_eq_true (show x ≠ k - 1 by omega)]
      decide
    · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
        decide_eq_true (show x + 1 ≠ k by omega), decide_eq_true (show x ≠ k - 1 by omega)]
      decide

theorem state_ge (n : ℕ) (hn : 1 ≤ n) : state 175 n = fun x => decide (x ≠ 2 - (n : ℤ)) := by
  induction n, hn using Nat.le_induction with
  | base => simpa using state_one
  | succ n hn ih =>
    rw [state_succ n _ ih]
    funext x
    push_cast
    congr 2
    ring

theorem c_ge (n : ℕ) (hn : 3 ≤ n) : c n = 1 := by
  rw [c, state_ge n (by omega)]
  simp only [ne_eq, decide_not]
  rw [decide_eq_false (show ¬ ((0 : ℤ) = 2 - (n : ℤ)) by omega)]
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
theorem a1 : a 1 = 11 := by decide
theorem a2 : a 2 = 110 := by decide
theorem a3 : a 3 = 1101 := by decide

theorem a_step (n : ℕ) (hn : 2 ≤ n) : a (n + 1) = 10 * a n + 1 := by
  rw [a_succ, c_ge (n + 1) (by omega)]

theorem recurrence (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  have h1 : a (k + 4) = 10 * a (k + 3) + 1 := a_step (k + 3) (by omega)
  have h2 : a (k + 3) = 10 * a (k + 2) + 1 := a_step (k + 2) (by omega)
  rw [h1, h2]
  push_cast
  ring

theorem gf_mul : A * ((1 - X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 3 := by
  have hD : A * ((1 - X) * (1 - 10 * X)) = A - C 11 * (A * X ^ 1) + C 10 * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - X ^ 2 + X ^ 3 : ℚ⟦X⟧) = C 1 * X ^ 0 - C 1 * X ^ 2 + C 1 * X ^ 3 := by
    simp only [map_one]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2, a3]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 11 * a (m - 1) - 10 * a (m - 2) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have g0 : m ≠ 0 := by omega
    have g2 : m ≠ 2 := by omega
    have g3 : m ≠ 3 := by omega
    have h3 : 3 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    simp only [h1, h2, h3, Nat.zero_le, k0, k2, k3, coeff_C, if_true, if_false, hq]
    ring

end OMA.S_oeis_a266680

theorem OMA.solution : type_of% @OMA.S_oeis_a266680.main := by
  refine ⟨OMA.S_oeis_a266680.recurrence, ?_⟩
  have h0 : PowerSeries.constantCoeff
      ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
  rw [← OMA.S_oeis_a266680.gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]
