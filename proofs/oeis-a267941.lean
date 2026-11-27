import OMAStatements.S_oeis_a267941
import Mathlib

namespace A267941
open OMA.S_oeis_a267941 PowerSeries in
lemma rule253 (l c r : Bool) :
    Nat.testBit 253 (4 * l.toNat + 2 * c.toNat + r.toNat) = (l || c || !r) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267941 PowerSeries in
lemma state_one (x : ℤ) : state 253 1 x = decide (x ≠ -1) := by
  show step 253 (state 253 0) x = _
  unfold step
  rw [rule253]
  show (decide (x - 1 = 0) || decide (x = 0) || !decide (x + 1 = 0)) = decide (x ≠ -1)
  by_cases h : x = -1
  · subst h
    decide
  · have h1 : x + 1 ≠ 0 := by omega
    simp [h, h1]

open OMA.S_oeis_a267941 PowerSeries in
lemma state_ge_two (n : ℕ) : ∀ x : ℤ, state 253 (n + 2) x = true := by
  induction n with
  | zero =>
    intro x
    show step 253 (state 253 1) x = true
    unfold step
    rw [rule253, state_one, state_one, state_one]
    by_cases h : x = -1
    · subst h
      decide
    · simp [h]
  | succ n ih =>
    intro x
    show step 253 (state 253 (n + 2)) x = true
    unfold step
    rw [rule253, ih, ih, ih]
    rfl

open OMA.S_oeis_a267941 PowerSeries in
lemma geom2 (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

open OMA.S_oeis_a267941 PowerSeries in
lemma a_ge_two (n : ℕ) : a (n + 2) + 1 = 2 ^ (2 * (n + 2) + 1) := by
  unfold a rowValue
  rw [← geom2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [state_ge_two]
  simp

open OMA.S_oeis_a267941 PowerSeries in
lemma a_zero : a 0 = 1 := by decide

open OMA.S_oeis_a267941 PowerSeries in
lemma a_one : a 1 = 3 := by decide

open OMA.S_oeis_a267941 PowerSeries in
lemma a_cast (n : ℕ) : ((a (n + 2) : ℕ) : ℚ) = 2 ^ (2 * (n + 2) + 1) - 1 := by
  have h := a_ge_two n
  have h' : ((a (n + 2) + 1 : ℕ) : ℚ) = ((2 ^ (2 * (n + 2) + 1) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a267941 PowerSeries in
lemma a_castZ (n : ℕ) : ((a (n + 2) : ℕ) : ℤ) = 2 ^ (2 * (n + 2) + 1) - 1 := by
  have h := a_ge_two n
  have h' : ((a (n + 2) + 1 : ℕ) : ℤ) = ((2 ^ (2 * (n + 2) + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a267941 PowerSeries in
lemma coeff_lhs (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (f * ((1 - X) * (1 - 4 * X)))
      = coeff n f - 5 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 4 * (if 2 ≤ n then coeff (n - 2) f else 0) := by
  have h5 : (C 5 : ℚ⟦X⟧) = 5 := map_ofNat C 5
  have h4 : (C 4 : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have e : f * ((1 - X) * (1 - 4 * X)) = f - C 5 * (X ^ 1 * f) + C 4 * (X ^ 2 * f) := by
    rw [h5, h4]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a267941 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3 : ℚ⟦X⟧)
      = (if n = 0 then 1 else 0) - (if n = 1 then 2 else 0) + (if n = 2 then 20 else 0)
        - (if n = 3 then 16 else 0) := by
  have h2 : (C 2 : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have h20 : (C 20 : ℚ⟦X⟧) = 20 := map_ofNat C 20
  have h16 : (C 16 : ℚ⟦X⟧) = 16 := map_ofNat C 16
  have e : (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3 : ℚ⟦X⟧)
      = X ^ 0 - C 2 * X ^ 1 + C 20 * X ^ 2 - C 16 * X ^ 3 := by
    rw [h2, h20, h16]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A267941

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267941.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have e1 : k + 4 - 1 = (k + 1) + 2 := by omega
    have e2 : k + 4 - 2 = k + 2 := by omega
    have e0 : k + 4 = (k + 2) + 2 := by omega
    rw [e1, e2, e0, A267941.a_castZ, A267941.a_castZ, A267941.a_castZ]
    ring
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    ext n
    rw [A267941.coeff_lhs, A267941.coeff_rhs]
    simp only [OMA.S_oeis_a267941.A, PowerSeries.coeff_mk]
    have v2 : ((OMA.S_oeis_a267941.a 2 : ℕ) : ℚ) = 31 := by
      have h := A267941.a_cast 0
      norm_num at h
      exact h
    have v3 : ((OMA.S_oeis_a267941.a 3 : ℕ) : ℚ) = 127 := by
      have h := A267941.a_cast 1
      norm_num at h
      exact h
    rcases lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · norm_num [A267941.a_zero]
      · norm_num [A267941.a_zero, A267941.a_one]
      · norm_num [A267941.a_zero, A267941.a_one, v2]
      · norm_num [A267941.a_one, v2, v3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have e1 : k + 4 - 1 = (k + 1) + 2 := by omega
      have e2 : k + 4 - 2 = k + 2 := by omega
      rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), e1, e2]
      have e0 : k + 4 = (k + 2) + 2 := by omega
      rw [e0, A267941.a_cast, A267941.a_cast, A267941.a_cast]
      ring
