import OMAStatements.S_oeis_a267044
import Mathlib

namespace A267044aux

open OMA.S_oeis_a267044 in
/-- Rule 91 as a function of the three neighbouring cells. -/
def r91 (l c r : Bool) : Bool := Nat.testBit 91 (4 * l.toNat + 2 * c.toNat + r.toNat)

open OMA.S_oeis_a267044 in
lemma step_eq (s : ℤ → Bool) (x : ℤ) :
    step 91 s x = r91 (s (x - 1)) (s x) (s (x + 1)) := rfl

open OMA.S_oeis_a267044 in
/-- Stage 2: ON exactly at -1 and 1. -/
def B2 : ℤ → Bool := fun x => decide (x = -1 ∨ x = 1)

open OMA.S_oeis_a267044 in
/-- Odd stages from 3 on: OFF exactly at -1, 0, 1. -/
def P : ℤ → Bool := fun x => decide (x < -1 ∨ 1 < x)

open OMA.S_oeis_a267044 in
/-- Even stages from 4 on: ON exactly at -2, ..., 2. -/
def Q : ℤ → Bool := fun x => decide (-2 ≤ x ∧ x ≤ 2)

open OMA.S_oeis_a267044 in
lemma step0 : step 91 (fun x : ℤ => decide (x = 0)) = fun x : ℤ => decide (x ≠ 0) := by
  funext x
  rw [step_eq]
  show r91 (decide (x - 1 = 0)) (decide (x = 0)) (decide (x + 1 = 0)) = decide (x ≠ 0)
  cases hb1 : decide (x - 1 = 0) <;> cases hb2 : decide (x = 0) <;>
    cases hb3 : decide (x + 1 = 0) <;> cases hb4 : decide (x ≠ 0) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a267044 in
lemma step1 : step 91 (fun x : ℤ => decide (x ≠ 0)) = B2 := by
  funext x
  rw [step_eq]
  show r91 (decide (x - 1 ≠ 0)) (decide (x ≠ 0)) (decide (x + 1 ≠ 0))
    = decide (x = -1 ∨ x = 1)
  cases hb1 : decide (x - 1 ≠ 0) <;> cases hb2 : decide (x ≠ 0) <;>
    cases hb3 : decide (x + 1 ≠ 0) <;> cases hb4 : decide (x = -1 ∨ x = 1) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a267044 in
lemma step2 : step 91 B2 = P := by
  funext x
  rw [step_eq]
  show r91 (decide (x - 1 = -1 ∨ x - 1 = 1)) (decide (x = -1 ∨ x = 1))
    (decide (x + 1 = -1 ∨ x + 1 = 1)) = decide (x < -1 ∨ 1 < x)
  cases hb1 : decide (x - 1 = -1 ∨ x - 1 = 1) <;> cases hb2 : decide (x = -1 ∨ x = 1) <;>
    cases hb3 : decide (x + 1 = -1 ∨ x + 1 = 1) <;> cases hb4 : decide (x < -1 ∨ 1 < x) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a267044 in
lemma stepP : step 91 P = Q := by
  funext x
  rw [step_eq]
  show r91 (decide (x - 1 < -1 ∨ 1 < x - 1)) (decide (x < -1 ∨ 1 < x))
    (decide (x + 1 < -1 ∨ 1 < x + 1)) = decide (-2 ≤ x ∧ x ≤ 2)
  cases hb1 : decide (x - 1 < -1 ∨ 1 < x - 1) <;> cases hb2 : decide (x < -1 ∨ 1 < x) <;>
    cases hb3 : decide (x + 1 < -1 ∨ 1 < x + 1) <;> cases hb4 : decide (-2 ≤ x ∧ x ≤ 2) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a267044 in
lemma stepQ : step 91 Q = P := by
  funext x
  rw [step_eq]
  show r91 (decide (-2 ≤ x - 1 ∧ x - 1 ≤ 2)) (decide (-2 ≤ x ∧ x ≤ 2))
    (decide (-2 ≤ x + 1 ∧ x + 1 ≤ 2)) = decide (x < -1 ∨ 1 < x)
  cases hb1 : decide (-2 ≤ x - 1 ∧ x - 1 ≤ 2) <;> cases hb2 : decide (-2 ≤ x ∧ x ≤ 2) <;>
    cases hb3 : decide (-2 ≤ x + 1 ∧ x + 1 ≤ 2) <;> cases hb4 : decide (x < -1 ∨ 1 < x) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a267044 in
lemma state_succ (n : ℕ) : state 91 (n + 1) = step 91 (state 91 n) := rfl

open OMA.S_oeis_a267044 in
lemma st1 : state 91 1 = fun x : ℤ => decide (x ≠ 0) := step0

open OMA.S_oeis_a267044 in
lemma st2 : state 91 2 = B2 := by
  rw [state_succ, st1]
  exact step1

open OMA.S_oeis_a267044 in
lemma st3 : state 91 3 = P := by
  rw [state_succ, st2]
  exact step2

open OMA.S_oeis_a267044 in
lemma st (j : ℕ) : state 91 (2 * j + 3) = P ∧ state 91 (2 * j + 4) = Q := by
  induction j with
  | zero =>
    refine ⟨st3, ?_⟩
    rw [state_succ, st3]
    exact stepP
  | succ j ih =>
    have h5 : state 91 (2 * (j + 1) + 3) = P := by
      rw [show 2 * (j + 1) + 3 = (2 * j + 4) + 1 by ring, state_succ, ih.2]
      exact stepQ
    refine ⟨h5, ?_⟩
    rw [show 2 * (j + 1) + 4 = (2 * (j + 1) + 3) + 1 by ring, state_succ, h5]
    exact stepP

open OMA.S_oeis_a267044 in
lemma c0 : c 0 = 1 := by decide

open OMA.S_oeis_a267044 in
lemma c1 : c 1 = 0 := by
  unfold c
  rw [st1]
  decide

open OMA.S_oeis_a267044 in
lemma c2 : c 2 = 0 := by
  unfold c
  rw [st2]
  decide

open OMA.S_oeis_a267044 in
lemma c_odd (j : ℕ) : c (2 * j + 3) = 0 := by
  unfold c
  rw [(st j).1]
  decide

open OMA.S_oeis_a267044 in
lemma c_even (j : ℕ) : c (2 * j + 4) = 1 := by
  unfold c
  rw [(st j).2]
  decide

open OMA.S_oeis_a267044 in
lemma c_shift (m : ℕ) : c (m + 5) = c (m + 3) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * j + 5 = 2 * (j + 1) + 3 by ring, c_odd, c_odd]
  · rw [show 2 * j + 1 + 5 = 2 * (j + 1) + 4 by ring, show 2 * j + 1 + 3 = 2 * j + 4 by ring,
      c_even, c_even]

open OMA.S_oeis_a267044 in
lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ _ (n + 1), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  · simp

open OMA.S_oeis_a267044 in
lemma a0 : a 0 = 1 := by
  unfold a
  simp [c0]

open OMA.S_oeis_a267044 in
lemma a1 : a 1 = 10 := by rw [a_succ, a0, c1]
open OMA.S_oeis_a267044 in
lemma a2 : a 2 = 100 := by rw [a_succ, a1, c2]
open OMA.S_oeis_a267044 in
lemma a3 : a 3 = 1000 := by
  have h : c 3 = 0 := c_odd 0
  rw [a_succ, a2, h]
open OMA.S_oeis_a267044 in
lemma a4 : a 4 = 10001 := by
  have h : c 4 = 1 := c_even 0
  rw [a_succ, a3, h]

open OMA.S_oeis_a267044 in
lemma rec5 (m : ℕ) : a (m + 5) + 10 * a (m + 2) = 10 * a (m + 4) + a (m + 3) := by
  have h1 : a (m + 5) = 10 * a (m + 4) + c (m + 5) := a_succ (m + 4)
  have h2 : a (m + 3) = 10 * a (m + 2) + c (m + 3) := a_succ (m + 2)
  have h3 := c_shift m
  omega

open OMA.S_oeis_a267044 in
lemma closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = (-550 + 450 * (-1) ^ n + 9901 * 10 ^ n) / 9900 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [a2]
    norm_num
  | succ n hn ih =>
    rw [a_succ]
    push_cast
    rw [ih]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e1 : (-1 : ℚ) ^ (2 * (i + 1)) = 1 := by
        rw [pow_mul]
        norm_num
      have e2 : (-1 : ℚ) ^ (2 * (i + 1) + 1) = -1 := by
        rw [pow_succ, e1]
        norm_num
      have hc : c (2 * (i + 1) + 1) = 0 := by
        rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
        exact c_odd i
      rw [e1, e2, hc]
      push_cast
      ring
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have e0 : (-1 : ℚ) ^ (2 * (i + 1)) = 1 := by
        rw [pow_mul]
        norm_num
      have e1 : (-1 : ℚ) ^ (2 * (i + 1) + 1) = -1 := by
        rw [pow_succ, e0]
        norm_num
      have e2 : (-1 : ℚ) ^ (2 * (i + 1) + 1 + 1) = 1 := by
        rw [pow_succ, e1]
        norm_num
      have hc : c (2 * (i + 1) + 1 + 1) = 1 := by
        rw [show 2 * (i + 1) + 1 + 1 = 2 * i + 4 by ring]
        exact c_even i
      rw [e1, e2, hc]
      push_cast
      ring

open OMA.S_oeis_a267044 in
lemma gf : A = (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 4)
    * ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X))⁻¹ := by
  have hD : PowerSeries.constantCoeff
      ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X) : PowerSeries ℚ)
      ≠ 0 := by simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  have h10 : (10 : PowerSeries ℚ) = PowerSeries.C (10 : ℚ) := (map_ofNat _ 10).symm
  have hL : A * ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X))
      = A - PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 1 * A) - PowerSeries.X ^ 2 * A
        + PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 3 * A) := by
    rw [← h10]
    ring
  rw [hL]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one, A, PowerSeries.coeff_mk]
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | h
  · simp [a0]
  · simp [a0, a1]
  · norm_num [a0, a1, a2]
  · norm_num [a0, a1, a2, a3]
  · norm_num [a0, a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    have hr : (a (m + 5) : ℚ) + 10 * (a (m + 2) : ℚ) = 10 * (a (m + 4) : ℚ) + (a (m + 3) : ℚ) := by
      exact_mod_cast rec5 m
    linarith

end A267044aux

theorem OMA.solution : type_of% @OMA.S_oeis_a267044.main := by
  refine ⟨?_, ?_, A267044aux.gf⟩
  · intro n hn
    exact A267044aux.closed n (by omega)
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    have hr : (OMA.S_oeis_a267044.a (m + 5) : ℤ) + 10 * (OMA.S_oeis_a267044.a (m + 2) : ℤ)
        = 10 * (OMA.S_oeis_a267044.a (m + 4) : ℤ) + (OMA.S_oeis_a267044.a (m + 3) : ℤ) := by
      exact_mod_cast A267044aux.rec5 m
    linarith
