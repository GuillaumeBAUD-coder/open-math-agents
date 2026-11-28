import OMAStatements.S_oeis_a267941

namespace OMA.S_oeis_a267941

open PowerSeries






/-- Barker's conjectures and the empirical closed form. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
  A = (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3) * ((1 - X) * (1 - 4 * X))⁻¹ ∧
  (∀ n : ℕ, 1 < n → a n = 2 ^ (2 * n + 1) - 1)

theorem state_one : state 253 1 = fun x => decide (x ≠ -1) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 by omega)]
    decide

theorem state_two : state 253 2 = fun _ => true := by
  funext x
  rw [show state 253 2 = step 253 (state 253 1) from rfl, state_one]
  simp only [step]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ 1 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ -1 by omega), decide_eq_true (show x ≠ -1 by omega),
      decide_eq_true (show x + 1 ≠ -1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ -1 by omega), decide_eq_true (show x ≠ -1 by omega),
      decide_eq_true (show x + 1 ≠ -1 by omega)]
    decide

theorem state_ge (n : ℕ) (hn : 2 ≤ n) : state 253 n = fun _ => true := by
  induction n, hn using Nat.le_induction with
  | base => exact state_two
  | succ n hn ih =>
    funext x
    rw [show state 253 (n + 1) = step 253 (state 253 n) from rfl, ih]
    simp only [step, Bool.toNat_true]
    decide

theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem a_ge (n : ℕ) (hn : 2 ≤ n) : a n = 2 ^ (2 * n + 1) - 1 := by
  rw [a, rowValue, state_ge n hn]
  simp only [Bool.toNat_true, one_mul]
  have := geom_two (2 * n + 1)
  omega

theorem a0 : a 0 = 1 := by decide
theorem a1 : a 1 = 3 := by
  rw [a, rowValue, state_one]
  decide

theorem recurrence (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [a_ge _ (by omega), a_ge _ (by omega), a_ge _ (by omega)]
  rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  have h1 : 1 ≤ 2 ^ (2 * (k + 4) + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (2 * (k + 3) + 1) := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ (2 * (k + 2) + 1) := Nat.one_le_two_pow
  push_cast [h1, h2, h3]
  ring

theorem gf_mul : A * ((1 - X) * (1 - 4 * X)) = 1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3 := by
  have hD : A * ((1 - X) * (1 - 4 * X)) = A - C 5 * (A * X ^ 1) + C 4 * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3 : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 2 * X ^ 1 + C 20 * X ^ 2 - C 16 * X ^ 3 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge m 4 with hm | hm
  · have e2 : a 2 = 31 := by rw [a_ge 2 le_rfl]; norm_num
    have e3 : a 3 = 127 := by rw [a_ge 3 (by norm_num)]; norm_num
    interval_cases m <;> norm_num [a0, a1, e2, e3]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 5 * a (m - 1) - 4 * a (m - 2) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have g0 : m ≠ 0 := by omega
    have g1 : m ≠ 1 := by omega
    have g2 : m ≠ 2 := by omega
    have g3 : m ≠ 3 := by omega
    have h3 : 3 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    simp only [h1, h2, h3, Nat.zero_le, g0, g1, g2, g3, k0, k1, k2, k3, coeff_C, if_true,
      if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨recurrence, ?_, fun n hn => a_ge n hn⟩
  have h0 : constantCoeff ((1 - X) * (1 - 4 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

end OMA.S_oeis_a267941

theorem OMA.solution : type_of% @OMA.S_oeis_a267941.main :=
  ⟨OMA.S_oeis_a267941.proof.1, OMA.S_oeis_a267941.proof.2.1⟩
