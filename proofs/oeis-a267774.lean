import OMAStatements.S_oeis_a267774
import Mathlib

namespace A267774
open OMA.S_oeis_a267774 PowerSeries in
lemma rule207 (l c r : Bool) :
    Nat.testBit 207 (4 * l.toNat + 2 * c.toNat + r.toNat) = (!l || c) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267774 PowerSeries in
lemma state_succ (n : ℕ) : ∀ x : ℤ, state 207 (n + 1) x = decide (x ≠ 1) := by
  induction n with
  | zero =>
    intro x
    show step 207 (state 207 0) x = _
    unfold step
    rw [rule207]
    show (!decide (x - 1 = 0) || decide (x = 0)) = decide (x ≠ 1)
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      ne_eq]
    omega
  | succ n ih =>
    intro x
    show step 207 (state 207 (n + 1)) x = _
    unfold step
    rw [rule207, ih, ih]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      ne_eq, not_not]
    omega

open OMA.S_oeis_a267774 PowerSeries in
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

open OMA.S_oeis_a267774 PowerSeries in
lemma geom2 (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

open OMA.S_oeis_a267774 PowerSeries in
lemma a_eq (n : ℕ) :
    a (n + 1) = ∑ i ∈ Finset.range (2 * n + 3), (if i ≠ n then 2 ^ i else 0) := by
  unfold a rowValue
  have e : 2 * (n + 1) + 1 = 2 * n + 3 := by ring
  rw [e]
  apply Finset.sum_congr rfl
  intro i _
  rw [state_succ]
  by_cases h : i = n
  · subst h
    simp
  · have h1 : (n : ℤ) + 1 - (i : ℤ) ≠ 1 := by omega
    simp [h1, h]

open OMA.S_oeis_a267774 PowerSeries in
lemma a_succ (n : ℕ) : a (n + 1) + 2 ^ n + 1 = 2 ^ (2 * n + 3) := by
  have h := sum_skip (2 * n + 3) n (by omega) (fun k => 2 ^ k)
  rw [a_eq, ← geom2 (2 * n + 3), ← h]

open OMA.S_oeis_a267774 PowerSeries in
lemma a_castZ (n : ℕ) : ((a (n + 1) : ℕ) : ℤ) = 2 ^ (2 * n + 3) - 2 ^ n - 1 := by
  have h := a_succ n
  have h' : ((a (n + 1) + 2 ^ n + 1 : ℕ) : ℤ) = ((2 ^ (2 * n + 3) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a267774 PowerSeries in
lemma a_cast (n : ℕ) : ((a (n + 1) : ℕ) : ℚ) = 2 ^ (2 * n + 3) - 2 ^ n - 1 := by
  have h := a_succ n
  have h' : ((a (n + 1) + 2 ^ n + 1 : ℕ) : ℚ) = ((2 ^ (2 * n + 3) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a267774 PowerSeries in
lemma a_zero : a 0 = 1 := by decide

open OMA.S_oeis_a267774 PowerSeries in
lemma coeff_lhs (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (f * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)))
      = coeff n f - 7 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 14 * (if 2 ≤ n then coeff (n - 2) f else 0)
        - 8 * (if 3 ≤ n then coeff (n - 3) f else 0) := by
  have h7 : (C 7 : ℚ⟦X⟧) = 7 := map_ofNat C 7
  have h14 : (C 14 : ℚ⟦X⟧) = 14 := map_ofNat C 14
  have h8 : (C 8 : ℚ⟦X⟧) = 8 := map_ofNat C 8
  have e : f * ((1 - X) * (1 - 2 * X) * (1 - 4 * X))
      = f - C 7 * (X ^ 1 * f) + C 14 * (X ^ 2 * f) - C 8 * (X ^ 3 * f) := by
    rw [h7, h14, h8]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a267774 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (1 - X + X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧)
      = (if n = 0 then 1 else 0) - (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0)
        - (if n = 3 then 4 else 0) := by
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have e : (1 - X + X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧)
      = X ^ 0 - X ^ 1 + X ^ 2 - C 4 * X ^ 3 := by
    rw [h4]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A267774

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267774.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have e1 : k + 4 - 1 = (k + 2) + 1 := by omega
    have e2 : k + 4 - 2 = (k + 1) + 1 := by omega
    have e3 : k + 4 - 3 = k + 1 := by omega
    have e0 : k + 4 = (k + 3) + 1 := by omega
    rw [e1, e2, e3, e0, A267774.a_castZ, A267774.a_castZ, A267774.a_castZ, A267774.a_castZ]
    ring
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    ext n
    rw [A267774.coeff_lhs, A267774.coeff_rhs]
    simp only [OMA.S_oeis_a267774.A, PowerSeries.coeff_mk]
    have v1 : ((OMA.S_oeis_a267774.a 1 : ℕ) : ℚ) = 6 := by
      have h := A267774.a_cast 0
      norm_num at h
      exact h
    have v2 : ((OMA.S_oeis_a267774.a 2 : ℕ) : ℚ) = 29 := by
      have h := A267774.a_cast 1
      norm_num at h
      exact h
    have v3 : ((OMA.S_oeis_a267774.a 3 : ℕ) : ℚ) = 123 := by
      have h := A267774.a_cast 2
      norm_num at h
      exact h
    rcases lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · norm_num [A267774.a_zero]
      · norm_num [A267774.a_zero, v1]
      · norm_num [A267774.a_zero, v1, v2]
      · norm_num [A267774.a_zero, v1, v2, v3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have e1 : k + 4 - 1 = (k + 2) + 1 := by omega
      have e2 : k + 4 - 2 = (k + 1) + 1 := by omega
      have e3 : k + 4 - 3 = k + 1 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), e1, e2, e3]
      have e0 : k + 4 = (k + 3) + 1 := by omega
      rw [e0, A267774.a_cast, A267774.a_cast, A267774.a_cast, A267774.a_cast]
      ring
