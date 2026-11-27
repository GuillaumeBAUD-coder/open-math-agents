import OMAStatements.S_oeis_a267461
import Mathlib

namespace A267461
open OMA.S_oeis_a267461 PowerSeries in
lemma eca133 (l c r : Bool) :
    (eca 133 l c r = true) ↔ ((¬ l = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267461 PowerSeries in
lemma st (t : ℕ) : ∀ x : ℤ, (state (t + 1) x = true ↔
    ((x < -((t : ℤ) + 1) ∨ (t : ℤ) + 1 < x) ∨ x = 0 ∨
      (x % 2 = 0 ∧ -((t : ℤ) + 1) + 2 ≤ x ∧ x + 2 ≤ (t : ℤ) + 1))) := by
  induction t with
  | zero =>
    intro x
    show eca 133 (state 0 (x - 1)) (state 0 x) (state 0 (x + 1)) = true ↔ _
    rw [eca133]
    show ((¬ decide (x - 1 = 0) = true ∧ ¬ decide (x + 1 = 0) = true) ∨
      (decide (x - 1 = 0) = true ∧ decide (x = 0) = true ∧ decide (x + 1 = 0) = true)) ↔ _
    simp only [decide_eq_true_eq]
    push_cast
    omega
  | succ t ih =>
    intro x
    show eca 133 (state (t + 1) (x - 1)) (state (t + 1) x) (state (t + 1) (x + 1)) = true ↔ _
    rw [eca133, ih, ih, ih]
    push_cast
    omega

open OMA.S_oeis_a267461 PowerSeries in
lemma off_iff (v k : ℕ) (hv : 1 ≤ v) (hk : k < 2 * (v + 1) + 1) :
    state (v + 1) ((k : ℤ) - ((v + 1 : ℕ) : ℤ)) = false ↔
      ((k + (v + 1)) % 2 = 1 ∨ ((k + (v + 1)) % 2 = 0 ∧ (k < 2 ∨ 2 * (v + 1) - 2 < k))) := by
  rw [← Bool.not_eq_true, st v]
  push_cast
  omega

open OMA.S_oeis_a267461 PowerSeries in
lemma cardA (t m : ℕ) :
    ((Finset.range m).filter (fun k => (k + t) % 2 = 1)).card = (m + t % 2) / 2 := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    omega
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      omega
    · rw [ih]
      omega

open OMA.S_oeis_a267461 PowerSeries in
lemma cardB (t : ℕ) (ht : 2 ≤ t) :
    ((Finset.range (2 * t + 1)).filter
      (fun k => (k + t) % 2 = 0 ∧ (k < 2 ∨ 2 * t - 2 < k))).card = 2 := by
  have h : (Finset.range (2 * t + 1)).filter
      (fun k => (k + t) % 2 = 0 ∧ (k < 2 ∨ 2 * t - 2 < k)) = {t % 2, 2 * t - t % 2} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h, Finset.card_pair (by omega)]

open OMA.S_oeis_a267461 PowerSeries in
lemma white_ge2 (v : ℕ) (hv : 1 ≤ v) : white (v + 1) = 2 * ((v + 2) / 2) + 2 := by
  unfold white
  rw [Finset.filter_congr (fun k hk => off_iff v k hv (Finset.mem_range.mp hk)),
    Finset.filter_or,
    Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun k _ h1 h2 => by omega)),
    cardA, cardB (v + 1) (by omega)]
  omega

open OMA.S_oeis_a267461 PowerSeries in
lemma white_zero : white 0 = 0 := by decide

open OMA.S_oeis_a267461 PowerSeries in
lemma white_one : white 1 = 2 := by decide

open OMA.S_oeis_a267461 PowerSeries in
lemma a_zero : a 0 = 0 := by
  unfold a
  simp [white_zero]

open OMA.S_oeis_a267461 PowerSeries in
lemma a_succ (n : ℕ) : a (n + 1) = a n + white (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a267461 PowerSeries in
lemma closed (n : ℕ) :
    4 * ((a (n + 1) : ℕ) : ℤ) = 2 * ((n : ℤ) + 1) ^ 2 + 12 * ((n : ℤ) + 1) - (-1) ^ (n + 1) - 7 := by
  induction n with
  | zero =>
    rw [a_succ, a_zero, white_one]
    norm_num
  | succ n ih =>
    have hpow1 : (-1 : ℤ) ^ (n + 1) = -(-1) ^ n := by ring
    have hpow2 : (-1 : ℤ) ^ (n + 1 + 1) = (-1) ^ n := by ring
    rw [hpow1] at ih
    rw [a_succ, white_ge2 (n + 1) (by omega), hpow2]
    rcases Nat.even_or_odd n with he | ho
    · have hs : (-1 : ℤ) ^ n = 1 := he.neg_one_pow
      have hw : 2 * ((n + 1 + 2) / 2) + 2 = n + 4 := by
        obtain ⟨m, rfl⟩ := he
        omega
      rw [hs] at ih
      rw [hw, hs]
      push_cast
      linarith
    · have hs : (-1 : ℤ) ^ n = -1 := ho.neg_one_pow
      have hw : 2 * ((n + 1 + 2) / 2) + 2 = n + 5 := by
        obtain ⟨m, rfl⟩ := ho
        omega
      rw [hs] at ih
      rw [hw, hs]
      push_cast
      linarith

open OMA.S_oeis_a267461 PowerSeries in
lemma rec5 (k : ℕ) :
    ((a (k + 5) : ℕ) : ℤ) = 2 * a (k + 4) - 2 * a (k + 2) + a (k + 1) := by
  have h1 := closed k
  have h2 := closed (k + 1)
  have h4 := closed (k + 3)
  have h5 := closed (k + 4)
  push_cast at h1 h2 h4 h5
  have key : 4 * (((a (k + 5) : ℕ) : ℤ) - (2 * a (k + 4) - 2 * a (k + 2) + a (k + 1))) = 0 := by
    linear_combination h5 - 2 * h4 + 2 * h2 - h1
  linarith

open OMA.S_oeis_a267461 PowerSeries in
lemma coeff_lhs (f : PowerSeries ℤ) (n : ℕ) :
    coeff n (f * ((1 - X) ^ 3 * (1 + X)))
      = coeff n f - 2 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 2 * (if 3 ≤ n then coeff (n - 3) f else 0)
        - (if 4 ≤ n then coeff (n - 4) f else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : f * ((1 - X) ^ 3 * (1 + X))
      = f - C 2 * (X ^ 1 * f) + C 2 * (X ^ 3 * f) - X ^ 4 * f := by
    rw [h2]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a267461 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (2 * X * (1 + X - X ^ 3) : PowerSeries ℤ)
      = (if n = 1 then 2 else 0) + (if n = 2 then 2 else 0) - (if n = 4 then 2 else 0) := by
  have h2 : (C 2 : PowerSeries ℤ) = 2 := map_ofNat C 2
  have e : (2 * X * (1 + X - X ^ 3) : PowerSeries ℤ)
      = C 2 * X ^ 1 + C 2 * X ^ 2 - C 2 * X ^ 4 := by
    rw [h2]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A267461

theorem OMA.solution : type_of% @OMA.S_oeis_a267461.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := A267461.closed m
    push_cast
    linarith
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    have e1 : k + 5 - 1 = k + 4 := by omega
    have e3 : k + 5 - 3 = k + 2 := by omega
    have e4 : k + 5 - 4 = k + 1 := by omega
    rw [e1, e3, e4]
    exact A267461.rec5 k
  · ext n
    rw [A267461.coeff_lhs, A267461.coeff_rhs]
    simp only [PowerSeries.coeff_mk]
    have v0 : ((OMA.S_oeis_a267461.a 0 : ℕ) : ℤ) = 0 := by
      rw [A267461.a_zero]
      rfl
    have v1 : ((OMA.S_oeis_a267461.a 1 : ℕ) : ℤ) = 2 := by
      have h := A267461.closed 0
      norm_num at h
      linarith
    have v2 : ((OMA.S_oeis_a267461.a 2 : ℕ) : ℤ) = 6 := by
      have h := A267461.closed 1
      norm_num at h
      linarith
    have v3 : ((OMA.S_oeis_a267461.a 3 : ℕ) : ℤ) = 12 := by
      have h := A267461.closed 2
      norm_num at h
      linarith
    have v4 : ((OMA.S_oeis_a267461.a 4 : ℕ) : ℤ) = 18 := by
      have h := A267461.closed 3
      norm_num at h
      linarith
    rcases lt_or_ge n 5 with hlt | hge
    · interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v1, v2]
      · norm_num [v0, v2, v3]
      · norm_num [v0, v1, v3, v4]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have e1 : k + 5 - 1 = k + 4 := by omega
      have e3 : k + 5 - 3 = k + 2 := by omega
      have e4 : k + 5 - 4 = k + 1 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), e1, e3, e4, A267461.rec5 k]
      ring
