import OMAStatements.S_oeis_a262779

-- Problem: A262779: Binary representation of the n-th iteration of the Rule 175 elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a262779.lean:0 (declaration OMA.S_oeis_a262779.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)
-- Proof idea: for t >= 1 every cell of Rule 175 is ON except the one at position 2 - t,
-- so a(n) = (10^(2n+1) - 1)/9 - 10^(2n-2) for n >= 1, i.e. 9 a(n+1) = 991 * 100^n - 1.

namespace OMA.P_a262779
open OMA.S_oeis_a262779 PowerSeries

lemma ruleOut_175 (l c r : Bool) : ruleOut 175 l c r = (!l || r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_succ (t : ℕ) (i : ℤ) : cell 175 (t + 1) i = decide (i ≠ 1 - t) := by
  induction t generalizing i with
  | zero =>
    simp only [cell, ruleOut_175]
    by_cases h : i = 1 <;> simp [h] <;> omega
  | succ t ih =>
    show ruleOut 175 (cell 175 (t + 1) (i - 1)) (cell 175 (t + 1) i) (cell 175 (t + 1) (i + 1)) = _
    rw [ruleOut_175, ih, ih]
    push_cast
    by_cases h1 : i - 1 = 1 - (t : ℤ) <;> by_cases h2 : i + 1 = 1 - (t : ℤ) <;>
      by_cases h3 : i = 1 - ((t : ℤ) + 1) <;> simp [h1, h2, h3] <;> omega

lemma a_succ (m : ℕ) :
    a (m + 1) = (∑ j ∈ Finset.range (2 * m + 3), (10 : ℤ) ^ j) - 10 ^ (2 * m) := by
  have h : ∀ j ∈ Finset.range (2 * (m + 1) + 1),
      (if cell 175 (m + 1) ((j : ℤ) - (m + 1 : ℕ)) then (10 : ℤ) ^ (2 * (m + 1) - j) else 0)
        = (10 : ℤ) ^ (2 * (m + 1) - j) - (if j = 2 then (10 : ℤ) ^ (2 * (m + 1) - j) else 0) := by
    intro j _
    rw [cell_succ]
    by_cases hj : j = 2
    · subst hj; simp; omega
    · simp [hj]; intro h; omega
  unfold a
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hm : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
  rw [if_pos (by simp), hm]
  congr 1
  · rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp at hj
    congr 1
    omega

lemma key (m : ℕ) : 9 * a (m + 1) = 991 * 100 ^ m - 1 := by
  rw [a_succ, mul_sub]
  have g := geom_sum_mul (10 : ℤ) (2 * m + 3)
  have e1 : (10 : ℤ) ^ (2 * m + 3) = 1000 * 100 ^ m := by
    rw [pow_add, pow_mul]; norm_num; ring
  have e2 : (10 : ℤ) ^ (2 * m) = 100 ^ m := by rw [pow_mul]; norm_num
  rw [e2]
  linear_combination g + e1

lemma a_zero : a 0 = 1 := by simp [a, cell]

lemma a_one : a 1 = 110 := by have := key 0; norm_num at this; omega

lemma a_two : a 2 = 11011 := by have := key 1; norm_num at this; omega

lemma recur (n : ℕ) (hn : n > 2) : a n = 101 * a (n - 1) - 100 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h2 := key (m + 2)
  have h1 := key (m + 1)
  have h0 := key m
  have e1 : m + 3 - 1 = (m + 1) + 1 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  rw [e1, e2]
  have : 9 * a (m + 3) = 9 * (101 * a (m + 1 + 1) - 100 * a (m + 1)) := by
    rw [show m + 3 = m + 2 + 1 by omega, h2, mul_sub, ← mul_assoc, ← mul_assoc,
      mul_comm 9 (101 : ℤ), mul_comm 9 (100 : ℤ), mul_assoc, mul_assoc, h1, h0]
    ring
  omega

end OMA.P_a262779

open OMA.S_oeis_a262779 OMA.P_a262779 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a262779.main := by
  refine ⟨recur, ?_⟩
  ext n
  have e : ((1 : PowerSeries ℚ) - X) * (1 - 100 * X) = 1 - C (101 : ℚ) * X + C (100 : ℚ) * X ^ 2 := by
    simp only [map_ofNat]; ring
  have e' : (1 + 9 * X + X ^ 2 : PowerSeries ℚ) = 1 + C (9 : ℚ) * X + X ^ 2 := by
    simp only [map_ofNat]
  rw [e']
  rw [e, mul_add, mul_sub, mul_one, mul_left_comm, mul_left_comm _ (C _)]
  rw [map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_mul_X_pow', ← pow_one X, coeff_mul_X_pow',
    map_add, map_add, coeff_C_mul]
  rcases n with _ | _ | _ | n
  · simp [a_zero]
  · simp [a_zero, a_one]; norm_num
  · simp [a_zero, a_one, a_two, coeff_X_pow, coeff_X]; norm_num
  · have := recur (n + 3) (by omega)
    simp only [coeff_mk, coeff_one, coeff_X_pow]
    simp
    have e1 : n + 3 - 1 = n + 2 := by omega
    have e2 : n + 3 - 2 = n + 1 := by omega
    rw [e1, e2] at this
    have : ((a (n + 3) : ℤ) : ℚ) = 101 * (a (n + 2) : ℚ) - 100 * (a (n + 1) : ℚ) := by
      rw [this]; push_cast; ring
    rw [this]; ring
