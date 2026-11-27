import OMAStatements.S_oeis_a266438
import Mathlib

namespace A266438
open OMA.S_oeis_a266438 PowerSeries in
lemma eca23 (l c r : Bool) :
    eca 23 l c r = ((!l && !c) || (!l && !r) || (!c && !r)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a266438 PowerSeries in
lemma state_succ (t : ℕ) : ∀ i : ℤ, state (t + 1) i = decide (t % 2 = 0) := by
  induction t with
  | zero =>
    intro i
    show eca 23 (state 0 (i - 1)) (state 0 i) (state 0 (i + 1)) = _
    rw [eca23]
    show ((!decide (i - 1 = 0) && !decide (i = 0)) || (!decide (i - 1 = 0) && !decide (i + 1 = 0))
      || (!decide (i = 0) && !decide (i + 1 = 0))) = true
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  | succ t ih =>
    intro i
    show eca 23 (state (t + 1) (i - 1)) (state (t + 1) i) (state (t + 1) (i + 1)) = _
    rw [eca23, ih, ih, ih]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, or_self, and_self]
    omega

open OMA.S_oeis_a266438 PowerSeries in
lemma black_zero : black 0 = 1 := by decide

open OMA.S_oeis_a266438 PowerSeries in
lemma black_succ (t : ℕ) : black (t + 1) = if t % 2 = 0 then 2 * t + 3 else 0 := by
  unfold black
  by_cases h : t % 2 = 0
  · rw [if_pos h, Finset.filter_true_of_mem]
    · rw [Finset.card_range]
      ring
    · intro i _
      rw [state_succ]
      simp [h]
  · rw [if_neg h, Finset.filter_false_of_mem]
    · simp
    · intro i _
      rw [state_succ]
      simp [h]

open OMA.S_oeis_a266438 PowerSeries in
lemma a_zero : a 0 = 1 := by
  unfold a
  simp [black_zero]

open OMA.S_oeis_a266438 PowerSeries in
lemma a_succ (n : ℕ) : a (n + 1) = a n + black (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a266438 PowerSeries in
lemma closed (n : ℕ) :
    2 * ((a n : ℕ) : ℤ) = (n : ℤ) ^ 2 + 2 * n - (-1) ^ n * (n + 1) + 3 := by
  induction n with
  | zero =>
    rw [a_zero]
    norm_num
  | succ n ih =>
    rw [a_succ, black_succ]
    rcases Nat.even_or_odd n with he | ho
    · have h2 : n % 2 = 0 := Nat.even_iff.mp he
      have hs : (-1 : ℤ) ^ n = 1 := he.neg_one_pow
      rw [if_pos h2]
      rw [hs] at ih
      rw [pow_succ (-1 : ℤ) n, hs]
      push_cast
      linarith
    · have h2 : ¬ n % 2 = 0 := by
        have := Nat.odd_iff.mp ho
        omega
      have hs : (-1 : ℤ) ^ n = -1 := ho.neg_one_pow
      rw [if_neg h2]
      rw [hs] at ih
      rw [pow_succ (-1 : ℤ) n, hs]
      push_cast
      linarith

open OMA.S_oeis_a266438 PowerSeries in
lemma rec5 (k : ℕ) :
    ((a (k + 5) : ℕ) : ℤ) = a (k + 4) + 2 * a (k + 3) - 2 * a (k + 2) - a (k + 1) + a k := by
  have h0 := closed k
  have h1 := closed (k + 1)
  have h2 := closed (k + 2)
  have h3 := closed (k + 3)
  have h4 := closed (k + 4)
  have h5 := closed (k + 5)
  push_cast at h0 h1 h2 h3 h4 h5
  have key : 2 * (((a (k + 5) : ℕ) : ℤ)
      - (a (k + 4) + 2 * a (k + 3) - 2 * a (k + 2) - a (k + 1) + a k)) = 0 := by
    linear_combination h5 - h4 - 2 * h3 + 2 * h2 + h1 - h0
  linarith

open OMA.S_oeis_a266438 PowerSeries in
lemma coeff_lhs (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f * ((1 + X) ^ 2 * (1 - X) ^ 3))
      = coeff n f - (if 1 ≤ n then coeff (n - 1) f else 0)
        - 2 * (if 2 ≤ n then coeff (n - 2) f else 0)
        + 2 * (if 3 ≤ n then coeff (n - 3) f else 0)
        + (if 4 ≤ n then coeff (n - 4) f else 0)
        - (if 5 ≤ n then coeff (n - 5) f else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : f * ((1 + X) ^ 2 * (1 - X) ^ 3)
      = f - X ^ 1 * f - C 2 * (X ^ 2 * f) + C 2 * (X ^ 3 * f) + X ^ 4 * f - X ^ 5 * f := by
    rw [h2]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a266438 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ)
      = (if n = 0 then 1 else 0) + (if n = 1 then 3 else 0) - (if n = 2 then 2 else 0)
        + (if n = 3 then 1 else 0) + (if n = 4 then 1 else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have h3 : (C 3 : PowerSeries ℤ) = 3 := map_ofNat C 3
  have e : (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ)
      = X ^ 0 + C 3 * X ^ 1 - C 2 * X ^ 2 + X ^ 3 + X ^ 4 := by
    rw [h2, h3]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A266438

theorem OMA.solution : type_of% @OMA.S_oeis_a266438.main := by
  refine ⟨?_, A266438.closed, ?_⟩
  · ext n
    rw [A266438.coeff_lhs, A266438.coeff_rhs]
    simp only [PowerSeries.coeff_mk]
    have v0 : ((OMA.S_oeis_a266438.a 0 : ℕ) : ℤ) = 1 := by
      have h := A266438.closed 0
      norm_num at h
      linarith
    have v1 : ((OMA.S_oeis_a266438.a 1 : ℕ) : ℤ) = 4 := by
      have h := A266438.closed 1
      norm_num at h
      linarith
    have v2 : ((OMA.S_oeis_a266438.a 2 : ℕ) : ℤ) = 4 := by
      have h := A266438.closed 2
      norm_num at h
      linarith
    have v3 : ((OMA.S_oeis_a266438.a 3 : ℕ) : ℤ) = 11 := by
      have h := A266438.closed 3
      norm_num at h
      linarith
    have v4 : ((OMA.S_oeis_a266438.a 4 : ℕ) : ℤ) = 11 := by
      have h := A266438.closed 4
      norm_num at h
      linarith
    rcases lt_or_ge n 5 with hlt | hge
    · interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v0, v1, v2]
      · norm_num [v0, v1, v2, v3]
      · norm_num [v0, v1, v2, v3, v4]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have e1 : k + 5 - 1 = k + 4 := by omega
      have e2 : k + 5 - 2 = k + 3 := by omega
      have e3 : k + 5 - 3 = k + 2 := by omega
      have e4 : k + 5 - 4 = k + 1 := by omega
      have e5 : k + 5 - 5 = k := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), e1, e2, e3, e4, e5, A266438.rec5 k]
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    have e1 : k + 5 - 1 = k + 4 := by omega
    have e2 : k + 5 - 2 = k + 3 := by omega
    have e3 : k + 5 - 3 = k + 2 := by omega
    have e4 : k + 5 - 4 = k + 1 := by omega
    have e5 : k + 5 - 5 = k := by omega
    rw [e1, e2, e3, e4, e5]
    exact A266438.rec5 k
