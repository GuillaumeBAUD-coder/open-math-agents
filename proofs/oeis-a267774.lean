import OMAStatements.S_oeis_a267774

namespace OMA.S_oeis_a267774

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
  A = (1 - X + X ^ 2 - 4 * X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹

/-- The pattern from row 1 on: every cell ON except cell `1`. -/
def pat : ℤ → Bool := fun x => decide (x ≠ 1)

theorem state_one : state 207 1 = pat := by
  funext x
  simp only [state, step, pat]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide

theorem step_pat : step 207 pat = pat := by
  funext x
  simp only [step, pat]
  rcases (show x ≤ -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ 1 by omega), decide_eq_true (show x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ 1 by omega), decide_eq_true (show x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ 1 by omega)]
    decide

theorem state_ge (n : ℕ) (hn : 1 ≤ n) : state 207 n = pat := by
  induction n, hn using Nat.le_induction with
  | base => exact state_one
  | succ n hn ih => rw [show state 207 (n + 1) = step 207 (state 207 n) from rfl, ih, step_pat]

theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- `a(n) + 2^(n-1) + 1 = 2^(2n+1)` for `n >= 1`. -/
theorem a_ge (n : ℕ) (hn : 1 ≤ n) : a n + 2 ^ (n - 1) + 1 = 2 ^ (2 * n + 1) := by
  rw [a, rowValue, state_ge n hn]
  have hsplit : ∀ i ∈ Finset.range (2 * n + 1),
      (pat ((n : ℤ) - i)).toNat * 2 ^ i + (if i = n - 1 then 2 ^ i else 0) = 2 ^ i := by
    intro i hi
    by_cases h : i = n - 1
    · rw [if_pos h, pat, decide_eq_false (show ¬((n : ℤ) - (i : ℤ) ≠ 1) by omega)]
      simp
    · rw [if_neg h, pat, decide_eq_true (show (n : ℤ) - (i : ℤ) ≠ 1 by omega)]
      simp
  have hs : ∑ i ∈ Finset.range (2 * n + 1),
      ((pat ((n : ℤ) - i)).toNat * 2 ^ i + (if i = n - 1 then 2 ^ i else 0)) =
      ∑ i ∈ Finset.range (2 * n + 1), 2 ^ i := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (2 * n + 1)) (n - 1),
    if_pos (Finset.mem_range.2 (by omega))] at hs
  have hg := geom_two (2 * n + 1)
  omega

theorem a_int (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = 2 ^ (2 * n + 1) - 1 - 2 ^ (n - 1) := by
  have h := a_ge n hn
  have h' : ((a n + 2 ^ (n - 1) + 1 : ℕ) : ℤ) = ((2 ^ (2 * n + 1) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

theorem a0 : a 0 = 1 := by decide

theorem recurrence (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [a_int _ (by omega), a_int _ (by omega), a_int _ (by omega), a_int _ (by omega)]
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega,
    show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
  ring

theorem gf_mul : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = 1 - X + X ^ 2 - 4 * X ^ 3 := by
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - X + X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 1 * X ^ 1 + C 1 * X ^ 2 - C 4 * X ^ 3 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 4 with hm | hm
  · have e1 : (a 1 : ℤ) = 6 := by rw [a_int 1 le_rfl]; norm_num
    have e2 : (a 2 : ℤ) = 29 := by rw [a_int 2 (by norm_num)]; norm_num
    have e3 : (a 3 : ℤ) = 123 := by rw [a_int 3 (by norm_num)]; norm_num
    have f1 : (a 1 : ℚ) = 6 := by exact_mod_cast e1
    have f2 : (a 2 : ℚ) = 29 := by exact_mod_cast e2
    have f3 : (a 3 : ℚ) = 123 := by exact_mod_cast e3
    interval_cases m <;> norm_num [a0, f1, f2, f3]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 7 * a (m - 1) - 14 * a (m - 2) + 8 * a (m - 3) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    simp only [h1, h2, h3, Nat.zero_le, k0, k1, k2, k3, coeff_C, if_true, if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Control: the first terms listed in the entry. -/
theorem a_values : a 1 = 6 ∧ a 2 = 29 ∧ a 3 = 123 ∧ a 4 = 503 ∧ a 5 = 2031 := by
  have h1 := a_ge 1 le_rfl
  have h2 := a_ge 2 (by norm_num)
  have h3 := a_ge 3 (by norm_num)
  have h4 := a_ge 4 (by norm_num)
  have h5 := a_ge 5 (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  omega

end OMA.S_oeis_a267774

theorem OMA.solution : type_of% @OMA.S_oeis_a267774.main :=
  OMA.S_oeis_a267774.proof
