import OMAStatements.S_oeis_a266607
import Mathlib

namespace A266607
open OMA.S_oeis_a266607 PowerSeries in
lemma rule39 (l c r : Bool) :
    Nat.testBit 39 (4 * l.toNat + 2 * c.toNat + r.toNat)
      = ((!l && !c) || (!l && !r) || (l && !c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a266607 PowerSeries in
lemma state_pair (k : ℕ) :
    (∀ x : ℤ, state 39 (2 * k) x = decide (x = (k : ℤ))) ∧
    (∀ x : ℤ, state 39 (2 * k + 1) x = decide (x ≠ (k : ℤ) + 1)) := by
  induction k with
  | zero =>
    have h0 : ∀ x : ℤ, state 39 (2 * 0) x = decide (x = ((0 : ℕ) : ℤ)) := by
      intro x
      show decide (x = 0) = _
      simp
    refine ⟨h0, ?_⟩
    intro x
    show step 39 (state 39 (2 * 0)) x = _
    unfold step
    rw [rule39, h0, h0, h0, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, ne_eq]
    push_cast
    omega
  | succ k ih =>
    obtain ⟨_, ih2⟩ := ih
    have h0 : ∀ x : ℤ, state 39 (2 * (k + 1)) x = decide (x = ((k + 1 : ℕ) : ℤ)) := by
      intro x
      show step 39 (state 39 (2 * k + 1)) x = _
      unfold step
      rw [rule39, ih2, ih2, ih2, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, ne_eq, not_not]
      push_cast
      omega
    refine ⟨h0, ?_⟩
    intro x
    show step 39 (state 39 (2 * (k + 1))) x = _
    unfold step
    rw [rule39, h0, h0, h0, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, ne_eq]
    push_cast
    omega

open OMA.S_oeis_a266607 PowerSeries in
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

open OMA.S_oeis_a266607 PowerSeries in
lemma geom2 (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

open OMA.S_oeis_a266607 PowerSeries in
lemma a_even (k : ℕ) : a (2 * k) = 2 ^ k := by
  unfold a rowValue
  have h : ∀ i ∈ Finset.range (2 * (2 * k) + 1),
      (state 39 (2 * k) (((2 * k : ℕ) : ℤ) - (i : ℤ))).toNat * 2 ^ i
        = if i = k then 2 ^ i else 0 := by
    intro i _
    rw [(state_pair k).1]
    by_cases h : i = k
    · subst h
      have e : (2 : ℤ) * (i : ℤ) - (i : ℤ) = (i : ℤ) := by ring
      simp [e]
    · have h1 : ¬ ((2 : ℤ) * (k : ℤ) - (i : ℤ) = (k : ℤ)) := by omega
      simp [h1, h]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  have hk : k ∈ Finset.range (2 * (2 * k) + 1) := by
    rw [Finset.mem_range]
    omega
  rw [if_pos hk]

open OMA.S_oeis_a266607 PowerSeries in
lemma a_odd_eq (k : ℕ) :
    a (2 * k + 1) = ∑ i ∈ Finset.range (4 * k + 3), (if i ≠ k then 2 ^ i else 0) := by
  unfold a rowValue
  have e : 2 * (2 * k + 1) + 1 = 4 * k + 3 := by ring
  rw [e]
  apply Finset.sum_congr rfl
  intro i _
  rw [(state_pair k).2]
  by_cases h : i = k
  · subst h
    have e : (2 : ℤ) * (i : ℤ) + 1 - (i : ℤ) = (i : ℤ) + 1 := by ring
    simp [e]
  · have h1 : (2 : ℤ) * (k : ℤ) + 1 - (i : ℤ) ≠ (k : ℤ) + 1 := by omega
    simp [h1, h]

open OMA.S_oeis_a266607 PowerSeries in
lemma a_odd (k : ℕ) : a (2 * k + 1) + 2 ^ k + 1 = 2 ^ (4 * k + 3) := by
  have h := sum_skip (4 * k + 3) k (by omega) (fun i => 2 ^ i)
  rw [a_odd_eq, ← geom2 (4 * k + 3), ← h]

open OMA.S_oeis_a266607 PowerSeries in
lemma a_evenZ (k : ℕ) : ((a (2 * k) : ℕ) : ℤ) = 2 ^ k := by
  rw [a_even]
  push_cast
  ring

open OMA.S_oeis_a266607 PowerSeries in
lemma a_evenQ (k : ℕ) : ((a (2 * k) : ℕ) : ℚ) = 2 ^ k := by
  rw [a_even]
  push_cast
  ring

open OMA.S_oeis_a266607 PowerSeries in
lemma a_oddZ (k : ℕ) : ((a (2 * k + 1) : ℕ) : ℤ) = 2 ^ (4 * k + 3) - 2 ^ k - 1 := by
  have h := a_odd k
  have h' : ((a (2 * k + 1) + 2 ^ k + 1 : ℕ) : ℤ) = ((2 ^ (4 * k + 3) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a266607 PowerSeries in
lemma a_oddQ (k : ℕ) : ((a (2 * k + 1) : ℕ) : ℚ) = 2 ^ (4 * k + 3) - 2 ^ k - 1 := by
  have h := a_odd k
  have h' : ((a (2 * k + 1) + 2 ^ k + 1 : ℕ) : ℚ) = ((2 ^ (4 * k + 3) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a266607 PowerSeries in
lemma coeff_lhs (f : ℚ⟦X⟧) (n : ℕ) :
    coeff n (f * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)))
      = coeff n f - 19 * (if 2 ≤ n then coeff (n - 2) f else 0)
        + 50 * (if 4 ≤ n then coeff (n - 4) f else 0)
        - 32 * (if 6 ≤ n then coeff (n - 6) f else 0) := by
  have h19 : (C 19 : ℚ⟦X⟧) = 19 := map_ofNat C 19
  have h50 : (C 50 : ℚ⟦X⟧) = 50 := map_ofNat C 50
  have h32 : (C 32 : ℚ⟦X⟧) = 32 := map_ofNat C 32
  have e : f * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))
      = f - C 19 * (X ^ 2 * f) + C 50 * (X ^ 4 * f) - C 32 * (X ^ 6 * f) := by
    rw [h19, h50, h32]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

open OMA.S_oeis_a266607 PowerSeries in
lemma coeff_rhs (n : ℕ) :
    coeff n (1 + 6 * X - 17 * X ^ 2 + 11 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5 : ℚ⟦X⟧)
      = (if n = 0 then 1 else 0) + (if n = 1 then 6 else 0) - (if n = 2 then 17 else 0)
        + (if n = 3 then 11 else 0) + (if n = 4 then 16 else 0) - (if n = 5 then 32 else 0) := by
  have h6 : (C 6 : ℚ⟦X⟧) = 6 := map_ofNat C 6
  have h17 : (C 17 : ℚ⟦X⟧) = 17 := map_ofNat C 17
  have h11 : (C 11 : ℚ⟦X⟧) = 11 := map_ofNat C 11
  have h16 : (C 16 : ℚ⟦X⟧) = 16 := map_ofNat C 16
  have h32 : (C 32 : ℚ⟦X⟧) = 32 := map_ofNat C 32
  have e : (1 + 6 * X - 17 * X ^ 2 + 11 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5 : ℚ⟦X⟧)
      = X ^ 0 + C 6 * X ^ 1 - C 17 * X ^ 2 + C 11 * X ^ 3 + C 16 * X ^ 4 - C 32 * X ^ 5 := by
    rw [h6, h17, h11, h16, h32]
    ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  simp

end A266607

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a266607.main := by
  constructor
  · intro n hn
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      have e1 : 2 * (j + 3) - 2 = 2 * (j + 2) := by omega
      have e2 : 2 * (j + 3) - 4 = 2 * (j + 1) := by omega
      have e3 : 2 * (j + 3) - 6 = 2 * j := by omega
      rw [e1, e2, e3, A266607.a_evenZ, A266607.a_evenZ, A266607.a_evenZ, A266607.a_evenZ]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      have e1 : 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 := by omega
      have e2 : 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 := by omega
      have e3 : 2 * (j + 3) + 1 - 6 = 2 * j + 1 := by omega
      rw [e1, e2, e3, A266607.a_oddZ, A266607.a_oddZ, A266607.a_oddZ, A266607.a_oddZ]
      ring
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    ext n
    rw [A266607.coeff_lhs, A266607.coeff_rhs]
    simp only [OMA.S_oeis_a266607.A, PowerSeries.coeff_mk]
    have v0 : ((OMA.S_oeis_a266607.a 0 : ℕ) : ℚ) = 1 := by
      have h := A266607.a_evenQ 0
      norm_num at h
      exact_mod_cast h
    have v1 : ((OMA.S_oeis_a266607.a 1 : ℕ) : ℚ) = 6 := by
      have h := A266607.a_oddQ 0
      norm_num at h
      exact_mod_cast h
    have v2 : ((OMA.S_oeis_a266607.a 2 : ℕ) : ℚ) = 2 := by
      have h := A266607.a_evenQ 1
      norm_num at h
      exact_mod_cast h
    have v3 : ((OMA.S_oeis_a266607.a 3 : ℕ) : ℚ) = 125 := by
      have h := A266607.a_oddQ 1
      norm_num at h
      exact_mod_cast h
    have v4 : ((OMA.S_oeis_a266607.a 4 : ℕ) : ℚ) = 4 := by
      have h := A266607.a_evenQ 2
      norm_num at h
      exact_mod_cast h
    have v5 : ((OMA.S_oeis_a266607.a 5 : ℕ) : ℚ) = 2043 := by
      have h := A266607.a_oddQ 2
      norm_num at h
      exact_mod_cast h
    rcases lt_or_ge n 6 with hlt | hge
    · interval_cases n
      · norm_num [v0]
      · norm_num [v1]
      · norm_num [v0, v2]
      · norm_num [v1, v3]
      · norm_num [v0, v2, v4]
      · norm_num [v1, v3, v5]
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
        have e1 : 2 * (j + 3) - 2 = 2 * (j + 2) := by omega
        have e2 : 2 * (j + 3) - 4 = 2 * (j + 1) := by omega
        have e3 : 2 * (j + 3) - 6 = 2 * j := by omega
        rw [e1, e2, e3, A266607.a_evenQ, A266607.a_evenQ, A266607.a_evenQ, A266607.a_evenQ]
        ring
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
        have e1 : 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 := by omega
        have e2 : 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 := by omega
        have e3 : 2 * (j + 3) + 1 - 6 = 2 * j + 1 := by omega
        rw [e1, e2, e3, A266607.a_oddQ, A266607.a_oddQ, A266607.a_oddQ, A266607.a_oddQ]
        ring
