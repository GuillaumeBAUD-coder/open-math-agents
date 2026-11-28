import OMAStatements.S_oeis_a110515

namespace OMA.S_oeis_a110515

open PowerSeries



lemma G_mul : G * (1 - X ^ 4) = 1 - X + X ^ 2 + X ^ 3 := by
  have h : constantCoeff (1 - X ^ 4 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [G, mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

/-- The coefficient recursion `g(m) = c(m) + g(m-4)`. -/
lemma coeff_rec (m : ℕ) :
    coeff m G = coeff m (1 - X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) + if 4 ≤ m then coeff (m - 4) G else 0 := by
  have h := congrArg (coeff m) G_mul
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow'] at h
  rw [← h]
  ring

lemma coeff_G (m : ℕ) : coeff m G = if m % 4 = 1 then -1 else 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [coeff_rec]
    simp only [map_add, map_sub, coeff_one, coeff_X, coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> norm_num
    · rw [if_pos hm, ih (m - 4) (by omega)]
      have h1 : m ≠ 0 := by omega
      have h2 : m ≠ 1 := by omega
      have h3 : m ≠ 2 := by omega
      have h4 : m ≠ 3 := by omega
      have h5 : (m - 4) % 4 = m % 4 := by omega
      simp [h1, h2, h3, h4, h5]

lemma jacobi_value (m : ℕ) : jacobiSym ((2 : ℤ) ^ m) (2 * m + 1) = if m % 4 = 1 then -1 else 1 := by
  rw [jacobiSym.pow_left, jacobiSym.at_two (by exact ⟨m, by ring⟩)]
  have hchi := ZMod.χ₈_nat_eq_if_mod_eight (2 * m + 1)
  rw [hchi]
  have hodd : ¬ (2 * m + 1) % 2 = 0 := by omega
  rw [if_neg hodd]
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
  · have h8 : (2 * m + 1) % 8 = 1 := by omega
    simp [h8, h]
  · have h8 : (2 * m + 1) % 8 = 3 := by omega
    have hm : Odd m := Nat.odd_iff.mpr (by omega)
    simp [h8, h, hm.neg_one_pow]
  · have h8 : (2 * m + 1) % 8 = 5 := by omega
    have hm : Even m := Nat.even_iff.mpr (by omega)
    simp [h8, h, hm.neg_one_pow]
  · have h8 : (2 * m + 1) % 8 = 7 := by omega
    simp [h8, h]

/-- The conjectured formula: `T(n,k) = Jacobi(2^(n-k), 2(n-k)+1)` for `k ≤ n`, and `0` otherwise. -/
theorem conjecture (n k : ℕ) :
    T n k = if k ≤ n then ((jacobiSym ((2 : ℤ) ^ (n - k)) (2 * (n - k) + 1) : ℤ) : ℚ) else 0 := by
  unfold T
  split_ifs
  · rw [coeff_G, jacobi_value]
    split_ifs <;> norm_num
  · rfl

/-- Control: the first rows 1; -1, 1; 1, -1, 1; 1, 1, -1, 1. -/
example : T 0 0 = 1 ∧ T 1 0 = -1 ∧ T 2 0 = 1 ∧ T 3 0 = 1 ∧ T 3 1 = 1 ∧ T 3 2 = -1 := by
  simp only [T, coeff_G]
  norm_num

end OMA.S_oeis_a110515

theorem OMA.solution : type_of% @OMA.S_oeis_a110515.main :=
  fun n k => OMA.S_oeis_a110515.conjecture n k
