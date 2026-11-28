import OMAStatements.S_oeis_a267045
import Mathlib

open OMA.S_oeis_a267045

private def live (t : ℕ) (i : ℤ) : Prop :=
    (t = 0 ∧ (i = 0)) ∨
    (t = 1 ∧ (i ≠ 0)) ∨
    (t = 2 ∧ (i = -1 ∨ i = 1)) ∨
    (3 ≤ t ∧ t % 2 = 0 ∧ (-(t : ℤ) ≤ i ∧ i ≤ t ∧ (i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2))) ∨
    (3 ≤ t ∧ t % 2 = 1 ∧ ((-(t : ℤ) ≤ i ∧ i ≤ t ∧ ¬(i = -1 ∨ i = 0 ∨ i = 1)) ∨ ((i < -(t : ℤ) ∨ (t : ℤ) < i))))

private lemma table (l c r : Bool) :
    eca 91 l c r = true ↔ (c = false ∧ r = false) ∨ (l = false ∧ r = true) ∨ (l = true ∧ r = false) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 3 with h | h
    · simp only [live]
      interval_cases t <;> omega
    · simp only [live, eq_false (show ¬ t = 0 by omega), eq_false (show ¬ t = 1 by omega), eq_false (show ¬ t = 2 by omega), eq_false (show ¬ t + 1 = 0 by omega), eq_false (show ¬ t + 1 = 1 by omega), eq_false (show ¬ t + 1 = 2 by omega), eq_true (show 3 ≤ t by omega), eq_true (show 3 ≤ t + 1 by omega), false_and, false_or, or_false, true_and]
      omega


private lemma step (n : ℕ) : (a (n + 1) : ℤ) = (2 : ℤ) * a n + (if state (n + 1) 0 then 1 else 0) := by
  unfold a; push_cast; rw [Finset.sum_range_succ]; congr 1
  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t ht; simp at ht
    rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]; split_ifs <;> ring
  · simp

private lemma cen (t : ℕ) (ht : 3 ≤ t) : state (t + 2) 0 = state t 0 := by
  apply Bool.eq_iff_iff.mpr; rw [state_iff, state_iff]; unfold live; omega

private lemma v0 : a 0 = 1 := by decide

private lemma v1 : a 1 = 2 := by decide

private lemma v2 : a 2 = 4 := by decide

private lemma v3 : a 3 = 8 := by decide

private lemma v4 : a 4 = 17 := by decide

private lemma v5 : a 5 = 34 := by decide

private lemma v6 : a 6 = 69 := by decide

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma mzf (t : ℕ) (ht : 3 ≤ t) :
    2 * (if state t 0 then (1 : ℤ) else 0) = 1 + 1 * (-1) ^ t := by
  rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
  · rw [ev]
    have : state (2 * m) 0 = true := by
      rw [state_iff]; unfold live; omega
    simp [this]
  · rw [od]
    have : state (2 * m + 1) 0 = false := by
      rw [Bool.eq_false_iff]; intro hh; rw [state_iff] at hh; unfold live at hh; omega
    simp [this]

private lemma closedI (n : ℕ) (hn : 3 ≤ n) : 12 * (a n : ℤ) = 2 * (-1) ^ n + 13 * 2 ^ n - 6 := by
  induction n, hn using Nat.le_induction with
  | base => rw [v3]; norm_num
  | succ n hn ih =>
    have hs := step n
    have hm := mzf (n + 1) (by omega)
    rw [hs]
    linear_combination 2 * ih + (12 / 2 : ℤ) * hm

private lemma closedB (n : ℕ) (hn : 1 < n) : 12 * (a n : ℤ) = 2 * (-1) ^ n + 13 * 2 ^ n - 6 := by
  by_cases h : 3 ≤ n
  · exact closedI n h
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6]

private lemma recur (n : ℕ) (hn : 4 < n) : (a n : ℤ) = (2 : ℤ) * a (n - 1) + (1 : ℤ) * a (n - 2) + (-2 : ℤ) * a (n - 3) := by
  by_cases h : 5 < n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega]
    have h1 := step (m + 5)
    have h2 := step (m + 3)
    have h3 := cen (m + 4) (by omega)
    rw [show m + 5 + 1 = m + 6 by ring] at h1
    rw [show m + 3 + 1 = m + 4 by ring] at h2
    rw [show m + 4 + 2 = m + 6 by ring] at h3
    rw [h3] at h1
    linear_combination h1 - h2
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6]

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) = (1 - X ^ 2 + X ^ 4 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) * (1 + X) * (1 - 2 * X)) = F + (-2 : ℤ) • (F * X ^ 1) + (-1 : ℤ) • (F * X ^ 2) + (2 : ℤ) • (F * X ^ 3) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 - X ^ 2 + X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (-1 : ℤ) • X ^ 2 + (1 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6]

theorem OMA.solution : type_of% @OMA.S_oeis_a267045.main := by
  exact ⟨closedB, fun n hn => by have := recur n hn; linarith, gf⟩
