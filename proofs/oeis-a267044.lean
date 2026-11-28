import OMAStatements.S_oeis_a267044
import Mathlib

/-!
Rule 91 from a single ON cell: stage 1 is everything but cell 0, stage 2 is the cells -1 and 1,
and from stage 3 on the pattern has period 2: at odd stages every cell except -1, 0, 1 is ON, at
even stages exactly the cells -2..2 are ON. So the middle cell is ON at stage 0 and at the even
stages >= 4. With a(n+1) = 10 a(n) + c(n+1) this gives the closed form, the recurrence and the
generating function.
-/

namespace R91
open OMA.S_oeis_a267044 PowerSeries

theorem rule_true (l c r : Bool) :
    Nat.testBit 91 (4 * l.toNat + 2 * c.toNat + r.toNat) = true ↔
      ¬ ((l = true ∧ r = true) ∨ (l = false ∧ c = true ∧ r = false)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- Odd stages from 3 on. -/
def So (x : ℤ) : Bool := decide (x < -1 ∨ 1 < x)

/-- Even stages from 4 on. -/
def Se (x : ℤ) : Bool := decide (-2 ≤ x ∧ x ≤ 2)

theorem st1 : state 91 1 = fun x => decide (x ≠ 0) := by
  funext x
  show step 91 (state 91 0) x = _
  rw [Bool.eq_iff_iff]
  unfold step
  rw [rule_true]
  simp only [state, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem st2 : state 91 2 = fun x => decide (x = -1 ∨ x = 1) := by
  funext x
  show step 91 (state 91 1) x = _
  rw [st1, Bool.eq_iff_iff]
  unfold step
  rw [rule_true]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem st3 : state 91 3 = So := by
  funext x
  show step 91 (state 91 2) x = _
  rw [st2, Bool.eq_iff_iff]
  unfold step
  rw [rule_true]
  simp only [So, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem so_step : step 91 So = Se := by
  funext x
  rw [Bool.eq_iff_iff]
  unfold step
  rw [rule_true]
  simp only [So, Se, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem se_step : step 91 Se = So := by
  funext x
  rw [Bool.eq_iff_iff]
  unfold step
  rw [rule_true]
  simp only [So, Se, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem state_big (j : ℕ) : state 91 (2 * j + 3) = So ∧ state 91 (2 * j + 4) = Se := by
  induction j with
  | zero => exact ⟨st3, (congrArg (step 91) st3).trans so_step⟩
  | succ j ih =>
    have h5 : state 91 (2 * (j + 1) + 3) = So := by
      rw [show 2 * (j + 1) + 3 = 2 * j + 4 + 1 by ring]
      exact (congrArg (step 91) ih.2).trans se_step
    refine ⟨h5, ?_⟩
    rw [show 2 * (j + 1) + 4 = 2 * (j + 1) + 3 + 1 by ring]
    exact (congrArg (step 91) h5).trans so_step

theorem c_eq (k : ℕ) : c k = if k = 0 ∨ (4 ≤ k ∧ k % 2 = 0) then 1 else 0 := by
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · subst hj
      have hn : ¬ (2 * j + 3 = 0 ∨ (4 ≤ 2 * j + 3 ∧ (2 * j + 3) % 2 = 0)) := by omega
      rw [show 2 * j + 1 + 1 + 1 = 2 * j + 3 by ring, if_neg hn]
      unfold c
      rw [(state_big j).1]
      decide
    · subst hj
      have hp : 2 * j + 4 = 0 ∨ (4 ≤ 2 * j + 4 ∧ (2 * j + 4) % 2 = 0) := by omega
      rw [show 2 * j + 1 + 1 + 1 + 1 = 2 * j + 4 by ring, if_pos hp]
      unfold c
      rw [(state_big j).2]
      decide

theorem next_a (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [show n + 1 - t = n - t + 1 by omega, pow_succ]
    ring
  · simp

theorem a2 : a 2 = 100 := by decide

theorem closed (m : ℕ) :
    (a (m + 2) : ℚ) = (-550 + 450 * (-1) ^ (m + 2) + 9901 * 10 ^ (m + 2)) / 9900 := by
  induction m with
  | zero => rw [a2]; norm_num
  | succ m ih =>
    rw [show m + 1 + 2 = m + 2 + 1 by ring, next_a]
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hc : c (m + 2 + 1) = 0 := by rw [c_eq]; exact if_neg (by omega)
      have e1 : (-1 : ℚ) ^ (m + 2) = 1 := Even.neg_one_pow ⟨j + 1, by omega⟩
      have e2 : (-1 : ℚ) ^ (m + 2 + 1) = -1 := Odd.neg_one_pow ⟨j + 1, by omega⟩
      rw [hc]
      push_cast
      rw [ih, e1, e2]
      ring
    · have hc : c (m + 2 + 1) = 1 := by rw [c_eq]; exact if_pos (by omega)
      have e1 : (-1 : ℚ) ^ (m + 2) = -1 := Odd.neg_one_pow ⟨j + 1, by omega⟩
      have e2 : (-1 : ℚ) ^ (m + 2 + 1) = 1 := Even.neg_one_pow ⟨j + 2, by omega⟩
      rw [hc]
      push_cast
      rw [ih, e1, e2]
      ring

theorem c_two (k : ℕ) (hk : 3 ≤ k) : c (k + 2) = c k := by
  rw [c_eq, c_eq]
  by_cases h : k % 2 = 0
  · have h1 : k + 2 = 0 ∨ (4 ≤ k + 2 ∧ (k + 2) % 2 = 0) := by omega
    have h2 : k = 0 ∨ (4 ≤ k ∧ k % 2 = 0) := by omega
    rw [if_pos h1, if_pos h2]
  · have h1 : ¬ (k + 2 = 0 ∨ (4 ≤ k + 2 ∧ (k + 2) % 2 = 0)) := by omega
    have h2 : ¬ (k = 0 ∨ (4 ≤ k ∧ k % 2 = 0)) := by omega
    rw [if_neg h1, if_neg h2]

theorem recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 1 := ⟨n - 5, by omega⟩
  rw [show m + 4 + 1 - 1 = m + 4 by omega, show m + 4 + 1 - 2 = m + 2 + 1 by omega,
    show m + 4 + 1 - 3 = m + 2 by omega]
  have h1 := next_a (m + 4)
  have h2 := next_a (m + 2)
  have hc : c (m + 4 + 1) = c (m + 2 + 1) := c_two (m + 2 + 1) (by omega)
  rw [h1, h2, hc]
  push_cast
  ring

theorem a0 : a 0 = 1 := by decide
theorem a1 : a 1 = 10 := by decide
theorem a3 : a 3 = 1000 := by decide
theorem a4 : a 4 = 10001 := by decide

end R91

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267044.main := by
  open OMA.S_oeis_a267044 R91 in
  refine ⟨?_, recur, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact closed m
  have q0 : (a 0 : ℚ) = 1 := by exact_mod_cast a0
  have q1 : (a 1 : ℚ) = 10 := by exact_mod_cast a1
  have q2 : (a 2 : ℚ) = 100 := by exact_mod_cast a2
  have q3 : (a 3 : ℚ) = 1000 := by exact_mod_cast a3
  have q4 : (a 4 : ℚ) = 10001 := by exact_mod_cast a4
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  rw [show ((1 - X) * (1 + X) * (1 - 10 * X) : ℚ⟦X⟧)
        = 1 - C 10 * X ^ 1 - X ^ 2 + C 10 * X ^ 3 by simp only [map_ofNat]; ring,
      show ∀ p : ℚ⟦X⟧, p * (1 - C 10 * X ^ 1 - X ^ 2 + C 10 * X ^ 3)
        = p - C 10 * (p * X ^ 1) - p * X ^ 2 + C 10 * (p * X ^ 3) from fun p => by ring]
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp [q0]
  · simp [q0, q1]
  · simp [q0, q1, q2] <;> norm_num
  · simp [q0, q1, q2, q3]; norm_num
  · simp [q1, q2, q3, q4]; norm_num
  · have h := recur (n + 5) (by omega)
    simp only [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega,
      show n + 5 - 3 = n + 2 by omega] at h
    have hq : (a (n + 5) : ℚ) = 10 * a (n + 4) + a (n + 3) - 10 * a (n + 2) := by
      exact_mod_cast h
    simp only [show n + 1 + 1 + 1 + 1 + 1 = n + 5 by ring]
    simp [hq] <;> ring
