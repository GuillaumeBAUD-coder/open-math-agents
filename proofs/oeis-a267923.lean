import OMAStatements.S_oeis_a267923
import Mathlib

namespace A267923
open OMA.S_oeis_a267923 PowerSeries in
lemma rule245 (l c r : Bool) : rule 245 l c r = (l || !r) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267923 PowerSeries in
lemma row_succ (n : ℕ) : ∀ x : ℤ, row 245 (n + 1) x = decide (x ≠ (n : ℤ) - 1) := by
  induction n with
  | zero =>
    intro x
    show rule 245 (row 245 0 (x - 1)) (row 245 0 x) (row 245 0 (x + 1)) = _
    rw [rule245]
    show (decide (x - 1 = 0) || !decide (x + 1 = 0)) = decide (x ≠ ((0 : ℕ) : ℤ) - 1)
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      ne_eq]
    push_cast
    omega
  | succ n ih =>
    intro x
    show rule 245 (row 245 (n + 1) (x - 1)) (row 245 (n + 1) x) (row 245 (n + 1) (x + 1)) = _
    rw [rule245, ih, ih]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      ne_eq, not_not]
    push_cast
    omega

open OMA.S_oeis_a267923 PowerSeries in
lemma sum_skip (m j : ℕ) (hj : j < m) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range m, (if i ≠ j then f i else 0) + f j = ∑ i ∈ Finset.range m, f i := by
  have h1 : ∑ i ∈ Finset.range m, (if i = j then f i else 0) = f j := by
    rw [Finset.sum_ite_eq']
    simp [hj]
  calc ∑ i ∈ Finset.range m, (if i ≠ j then f i else 0) + f j
      = ∑ i ∈ Finset.range m, (if i ≠ j then f i else 0)
        + ∑ i ∈ Finset.range m, (if i = j then f i else 0) := by rw [h1]
    _ = ∑ i ∈ Finset.range m, ((if i ≠ j then f i else 0) + (if i = j then f i else 0)) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ Finset.range m, f i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = j <;> simp [h]

open OMA.S_oeis_a267923 PowerSeries in
lemma geom10 (m : ℕ) : 9 * ∑ k ∈ Finset.range m, 10 ^ k + 1 = 10 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

open OMA.S_oeis_a267923 PowerSeries in
lemma a_eq (n : ℕ) :
    a (n + 1) = ∑ k ∈ Finset.range (2 * n + 3), (if k ≠ 2 then 10 ^ k else 0) := by
  unfold a
  have e : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
  rw [e]
  apply Finset.sum_congr rfl
  intro k _
  rw [row_succ]
  have hk : (((n + 1 : ℕ) : ℤ) - (k : ℤ) ≠ (n : ℤ) - 1) ↔ k ≠ 2 := by
    push_cast
    omega
  simp only [decide_eq_true_eq, hk]

open OMA.S_oeis_a267923 PowerSeries in
lemma a_succ (n : ℕ) : 9 * (a (n + 1) + 100) + 1 = 10 ^ (2 * n + 3) := by
  have h := sum_skip (2 * n + 3) 2 (by omega) (fun k => 10 ^ k)
  have h100 : (10 : ℕ) ^ 2 = 100 := by norm_num
  rw [h100] at h
  rw [a_eq, ← geom10, ← h]

open OMA.S_oeis_a267923 PowerSeries in
lemma a_castZ (n : ℕ) : 9 * ((a (n + 1) : ℕ) : ℤ) = 10 ^ (2 * n + 3) - 901 := by
  have h := a_succ n
  have h' : ((9 * (a (n + 1) + 100) + 1 : ℕ) : ℤ) = ((10 ^ (2 * n + 3) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a267923 PowerSeries in
lemma a_zero : a 0 = 1 := by decide

open OMA.S_oeis_a267923 PowerSeries in
lemma rec1 (k : ℕ) : ((a (k + 3) : ℕ) : ℤ) = 101 * a (k + 2) - 100 * a (k + 1) := by
  have h1 := a_castZ k
  have h2 := a_castZ (k + 1)
  have h3 := a_castZ (k + 2)
  have e2 : (10 : ℤ) ^ (2 * (k + 1) + 3) = 100 * 10 ^ (2 * k + 3) := by ring
  have e3 : (10 : ℤ) ^ (2 * (k + 2) + 3) = 10000 * 10 ^ (2 * k + 3) := by ring
  rw [e2] at h2
  rw [e3] at h3
  linarith

open OMA.S_oeis_a267923 PowerSeries in
lemma coeff_lhs (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f * ((1 - X) * (1 - 100 * X)))
      = coeff n f - 101 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 100 * (if 2 ≤ n then coeff (n - 2) f else 0) := by
  have h5 : (C 101 : PowerSeries ℤ) = 101 := map_ofNat C 101
  have h4 : (C 100 : PowerSeries ℤ) = 100 := map_ofNat C 100
  have e : f * ((1 - X) * (1 - 100 * X)) = f - C 101 * (X ^ 1 * f) + C 100 * (X ^ 2 * f) := by
    rw [h5, h4]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a267923 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (1 - 90 * X + 10000 * X ^ 2 : PowerSeries ℤ)
      = (if n = 0 then 1 else 0) - (if n = 1 then 90 else 0) + (if n = 2 then 10000 else 0) := by
  have h2 : (C 90 : PowerSeries ℤ) = 90 := map_ofNat C 90
  have h20 : (C 10000 : PowerSeries ℤ) = 10000 := map_ofNat C 10000
  have e : (1 - 90 * X + 10000 * X ^ 2 : PowerSeries ℤ)
      = X ^ 0 - C 90 * X ^ 1 + C 10000 * X ^ 2 := by
    rw [h2, h20]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A267923

theorem OMA.solution : type_of% @OMA.S_oeis_a267923.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have e1 : k + 3 - 1 = k + 2 := by omega
    have e2 : k + 3 - 2 = k + 1 := by omega
    rw [e1, e2]
    exact A267923.rec1 k
  · ext n
    rw [A267923.coeff_lhs, A267923.coeff_rhs]
    simp only [PowerSeries.coeff_mk]
    have v1 : ((OMA.S_oeis_a267923.a 1 : ℕ) : ℤ) = 11 := by
      have h := A267923.a_castZ 0
      norm_num at h
      linarith
    have v2 : ((OMA.S_oeis_a267923.a 2 : ℕ) : ℤ) = 11011 := by
      have h := A267923.a_castZ 1
      norm_num at h
      linarith
    rcases lt_or_ge n 3 with hlt | hge
    · interval_cases n
      · norm_num [A267923.a_zero]
      · norm_num [A267923.a_zero, v1]
      · norm_num [A267923.a_zero, v1, v2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have e1 : k + 3 - 1 = k + 2 := by omega
      have e2 : k + 3 - 2 = k + 1 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), e1, e2, A267923.rec1 k]
      ring
