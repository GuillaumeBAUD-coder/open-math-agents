import OMAStatements.S_oeis_a267262
import Mathlib

namespace A267262
open OMA.S_oeis_a267262 PowerSeries in
lemma rule111 (l c x : Bool) :
    (rule 111 l c x = true) ↔ (¬ l = true ∨ (c = true ↔ ¬ x = true)) := by
  cases l <;> cases c <;> cases x <;> decide

open OMA.S_oeis_a267262 PowerSeries in
lemma st (j : ℕ) :
    (∀ x : ℤ, (row 111 (2 * j) x = true ↔
      ((x = 2 * (j : ℤ) - 6 ∧ 0 ≤ x) ∨ (0 ≤ x ∧ 2 * (j : ℤ) - 4 ≤ x ∧ x ≤ 2 * (j : ℤ))))) ∧
    (∀ x : ℤ, (row 111 (2 * j + 1) x = true ↔
      ¬ (x = 2 * (j : ℤ) + 1 ∨ (2 * (j : ℤ) - 3 ≤ x ∧ x ≤ 2 * (j : ℤ) - 1 ∧ 1 ≤ x)))) := by
  induction j with
  | zero =>
    have h0 : ∀ x : ℤ, (row 111 (2 * 0) x = true ↔
        ((x = 2 * ((0 : ℕ) : ℤ) - 6 ∧ 0 ≤ x) ∨
          (0 ≤ x ∧ 2 * ((0 : ℕ) : ℤ) - 4 ≤ x ∧ x ≤ 2 * ((0 : ℕ) : ℤ)))) := by
      intro x
      show decide (x = 0) = true ↔ _
      simp only [decide_eq_true_eq]
      push_cast
      omega
    refine ⟨h0, ?_⟩
    intro x
    show rule 111 (row 111 (2 * 0) (x - 1)) (row 111 (2 * 0) x) (row 111 (2 * 0) (x + 1)) = true ↔ _
    rw [rule111, h0, h0, h0]
    push_cast
    omega
  | succ j ih =>
    obtain ⟨_, ihO⟩ := ih
    have hE : ∀ x : ℤ, (row 111 (2 * (j + 1)) x = true ↔
        ((x = 2 * ((j + 1 : ℕ) : ℤ) - 6 ∧ 0 ≤ x) ∨
          (0 ≤ x ∧ 2 * ((j + 1 : ℕ) : ℤ) - 4 ≤ x ∧ x ≤ 2 * ((j + 1 : ℕ) : ℤ)))) := by
      intro x
      show rule 111 (row 111 (2 * j + 1) (x - 1)) (row 111 (2 * j + 1) x)
        (row 111 (2 * j + 1) (x + 1)) = true ↔ _
      rw [rule111, ihO, ihO, ihO]
      push_cast
      omega
    refine ⟨hE, ?_⟩
    intro x
    show rule 111 (row 111 (2 * (j + 1)) (x - 1)) (row 111 (2 * (j + 1)) x)
      (row 111 (2 * (j + 1)) (x + 1)) = true ↔ _
    rw [rule111, hE, hE, hE]
    push_cast
    omega

open OMA.S_oeis_a267262 PowerSeries in
lemma off_odd (i : ℕ) : off (2 * (i + 2) + 1) = 4 := by
  unfold off
  have h : (Finset.range (2 * (2 * (i + 2) + 1) + 1)).filter
      (fun k : ℕ => row 111 (2 * (i + 2) + 1) ((k : ℤ) - ((2 * (i + 2) + 1 : ℕ) : ℤ)) = false)
      = {4 * i + 6, 4 * i + 7, 4 * i + 8, 4 * i + 10} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      ← Bool.not_eq_true, (st (i + 2)).2]
    push_cast
    omega
  rw [h, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_pair (by omega)]

open OMA.S_oeis_a267262 PowerSeries in
lemma off_even (i : ℕ) : off (2 * (i + 3)) = 4 * i + 7 := by
  unfold off
  have h : (Finset.range (2 * (2 * (i + 3)) + 1)).filter
      (fun k : ℕ => row 111 (2 * (i + 3)) ((k : ℤ) - ((2 * (i + 3) : ℕ) : ℤ)) = false)
      = (Finset.range (4 * i + 8)).erase (4 * i + 6) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, ← Bool.not_eq_true,
      (st (i + 3)).1]
    push_cast
    omega
  rw [h, Finset.card_erase_of_mem (by simp), Finset.card_range]
  omega

open OMA.S_oeis_a267262 PowerSeries in
lemma a_succ (n : ℕ) : a (n + 1) = a n + off (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a267262 PowerSeries in
lemma a_zero : a 0 = 0 := by decide

open OMA.S_oeis_a267262 PowerSeries in
lemma a_one : a 1 = 1 := by decide

open OMA.S_oeis_a267262 PowerSeries in
lemma a_two : a 2 = 3 := by decide

open OMA.S_oeis_a267262 PowerSeries in
lemma a_three : a 3 = 5 := by decide

open OMA.S_oeis_a267262 PowerSeries in
lemma a_four : a 4 = 9 := by decide

open OMA.S_oeis_a267262 PowerSeries in
lemma closed (m : ℕ) :
    2 * ((a (m + 4) : ℕ) : ℤ) = ((m : ℤ) + 4) ^ 2 + (-1) ^ m * (m : ℤ) + 2 := by
  induction m with
  | zero =>
    rw [a_four]
    norm_num
  | succ m ih =>
    have hpow : (-1 : ℤ) ^ (m + 1) = -(-1) ^ m := by ring
    have e : m + 1 + 4 = (m + 4) + 1 := by ring
    rw [e, a_succ, hpow]
    rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
    · have hs : (-1 : ℤ) ^ (2 * i) = 1 := Even.neg_one_pow ⟨i, by ring⟩
      have ho : off (2 * i + 4 + 1) = 4 := off_odd i
      rw [hs] at ih
      rw [ho, hs]
      push_cast at ih ⊢
      linarith
    · have hs : (-1 : ℤ) ^ (2 * i + 1) = -1 := Odd.neg_one_pow ⟨i, rfl⟩
      have ho : off (2 * i + 1 + 4 + 1) = 4 * i + 7 := off_even i
      rw [hs] at ih
      rw [ho, hs]
      push_cast at ih ⊢
      linarith

open OMA.S_oeis_a267262 PowerSeries in
lemma rec9 (k : ℕ) :
    ((a (k + 9) : ℕ) : ℤ)
      = a (k + 8) + 2 * a (k + 7) - 2 * a (k + 6) - a (k + 5) + a (k + 4) := by
  have h0 := closed k
  have h1 := closed (k + 1)
  have h2 := closed (k + 2)
  have h3 := closed (k + 3)
  have h4 := closed (k + 4)
  have h5 := closed (k + 5)
  push_cast at h0 h1 h2 h3 h4 h5
  have key : 2 * (((a (k + 9) : ℕ) : ℤ)
      - (a (k + 8) + 2 * a (k + 7) - 2 * a (k + 6) - a (k + 5) + a (k + 4))) = 0 := by
    linear_combination h5 - h4 - 2 * h3 + 2 * h2 + h1 - h0
  linarith

open OMA.S_oeis_a267262 PowerSeries in
lemma coeff_lhs (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f * ((1 - X) ^ 3 * (1 + X) ^ 2))
      = coeff n f - (if 1 ≤ n then coeff (n - 1) f else 0)
        - 2 * (if 2 ≤ n then coeff (n - 2) f else 0)
        + 2 * (if 3 ≤ n then coeff (n - 3) f else 0)
        + (if 4 ≤ n then coeff (n - 4) f else 0)
        - (if 5 ≤ n then coeff (n - 5) f else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : f * ((1 - X) ^ 3 * (1 + X) ^ 2)
      = f - X ^ 1 * f - C 2 * (X ^ 2 * f) + C 2 * (X ^ 3 * f) + X ^ 4 * f - X ^ 5 * f := by
    rw [h2]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a267262 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (X * (1 + 2 * X + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ)
      = (if n = 1 then 1 else 0) + (if n = 2 then 2 else 0) + (if n = 5 then 1 else 0)
        + (if n = 6 then 1 else 0) - (if n = 7 then 2 else 0) + (if n = 8 then 1 else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : (X * (1 + 2 * X + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℤ)
      = X ^ 1 + C 2 * X ^ 2 + X ^ 5 + X ^ 6 - C 2 * X ^ 7 + X ^ 8 := by
    rw [h2]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A267262

theorem OMA.solution : type_of% @OMA.S_oeis_a267262.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h := A267262.closed m
    have e : (-1 : ℤ) ^ (m + 4) = (-1) ^ m := by ring
    rw [e]
    push_cast
    linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have e1 : k + 9 - 1 = k + 8 := by omega
    have e2 : k + 9 - 2 = k + 7 := by omega
    have e3 : k + 9 - 3 = k + 6 := by omega
    have e4 : k + 9 - 4 = k + 5 := by omega
    have e5 : k + 9 - 5 = k + 4 := by omega
    rw [e1, e2, e3, e4, e5]
    exact A267262.rec9 k
  · ext n
    rw [A267262.coeff_lhs, A267262.coeff_rhs]
    simp only [PowerSeries.coeff_mk]
    have v0 : ((OMA.S_oeis_a267262.a 0 : ℕ) : ℤ) = 0 := by
      rw [A267262.a_zero]
      rfl
    have v1 : ((OMA.S_oeis_a267262.a 1 : ℕ) : ℤ) = 1 := by
      rw [A267262.a_one]
      rfl
    have v2 : ((OMA.S_oeis_a267262.a 2 : ℕ) : ℤ) = 3 := by
      rw [A267262.a_two]
      rfl
    have v3 : ((OMA.S_oeis_a267262.a 3 : ℕ) : ℤ) = 5 := by
      rw [A267262.a_three]
      rfl
    have v4 : ((OMA.S_oeis_a267262.a 4 : ℕ) : ℤ) = 9 := by
      rw [A267262.a_four]
      rfl
    have v5 : ((OMA.S_oeis_a267262.a 5 : ℕ) : ℤ) = 13 := by
      have h := A267262.closed 1
      norm_num at h
      linarith
    have v6 : ((OMA.S_oeis_a267262.a 6 : ℕ) : ℤ) = 20 := by
      have h := A267262.closed 2
      norm_num at h
      linarith
    have v7 : ((OMA.S_oeis_a267262.a 7 : ℕ) : ℤ) = 24 := by
      have h := A267262.closed 3
      norm_num at h
      linarith
    have v8 : ((OMA.S_oeis_a267262.a 8 : ℕ) : ℤ) = 35 := by
      have h := A267262.closed 4
      norm_num at h
      linarith
    rcases lt_or_ge n 9 with hlt | hge
    · interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v0, v1, v2]
      · norm_num [v0, v1, v2, v3]
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4, v5]
      · norm_num [v1, v2, v3, v4, v5, v6]
      · norm_num [v2, v3, v4, v5, v6, v7]
      · norm_num [v3, v4, v5, v6, v7, v8]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have e1 : k + 9 - 1 = k + 8 := by omega
      have e2 : k + 9 - 2 = k + 7 := by omega
      have e3 : k + 9 - 3 = k + 6 := by omega
      have e4 : k + 9 - 4 = k + 5 := by omega
      have e5 : k + 9 - 5 = k + 4 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), e1, e2, e3, e4, e5,
        A267262.rec9 k]
      ring
