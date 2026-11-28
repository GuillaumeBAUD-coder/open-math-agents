import OMAStatements.S_mse_3290080

/-- For a fixed exponent no larger than the base, increasing the base by
one multiplies the power by at most three. -/
private theorem next_base_bound {a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    (b + 1) ^ a ≤ 3 * b ^ a := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hratio : (a : ℝ) * (b : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hbR).mpr (by exact_mod_cast hab)
  have hstep : 1 + (b : ℝ)⁻¹ ≤ Real.exp ((b : ℝ)⁻¹) := by
    simpa only [add_comm] using (Real.add_one_le_exp ((b : ℝ)⁻¹))
  have hpow : (1 + (b : ℝ)⁻¹) ^ a ≤ (Real.exp ((b : ℝ)⁻¹)) ^ a :=
    pow_le_pow_left₀ (by positivity) hstep a
  rw [← Real.exp_nat_mul] at hpow
  have hbound : (1 + (b : ℝ)⁻¹) ^ a ≤ 3 :=
    hpow.trans ((Real.exp_le_exp.mpr hratio).trans Real.exp_one_lt_three.le)
  have hbpower : ((b : ℝ) + 1) ^ a ≤ 3 * (b : ℝ) ^ a := by
    calc
      ((b : ℝ) + 1) ^ a = ((b : ℝ) * (1 + (b : ℝ)⁻¹)) ^ a := by
        rw [mul_add, mul_one, mul_inv_cancel₀ hbR.ne']
      _ = (b : ℝ) ^ a * (1 + (b : ℝ)⁻¹) ^ a := mul_pow _ _ _
      _ ≤ 3 * (b : ℝ) ^ a := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ (b : ℝ) ^ a)
  exact_mod_cast hbpower

private theorem gap_for_three_or_more {a b : ℕ} (ha : 3 ≤ a) (hab : a < b) :
    b ^ a + a + b < a ^ b := by
  have hstart : a + 1 ≤ b := hab
  induction b, hstart using Nat.le_induction with
  | base =>
    by_cases h : a = 3
    · subst a
      norm_num
    · have ha4 : 4 ≤ a := by omega
      have hpow : a ^ 2 ≤ a ^ a := by gcongr <;> omega
      have hlin : 3 * a ≤ a ^ 2 := by
        simpa only [pow_two] using Nat.mul_le_mul_right a ha
      have hnext := next_base_bound (a := a) (b := a) (by omega) le_rfl
      calc
        (a + 1) ^ a + a + (a + 1) < 4 * a ^ a := by omega
        _ ≤ a * a ^ a := Nat.mul_le_mul_right _ ha4
        _ = a ^ (a + 1) := by rw [pow_succ, mul_comm]
  | succ b hb ih =>
    have hnext := next_base_bound (a := a) (b := b) (by omega) (by omega)
    have h1 : 3 * b ^ a ≤ a * b ^ a := Nat.mul_le_mul_right _ ha
    have h2 : a + (b + 1) ≤ a * (a + b) := by
      have h := Nat.mul_le_mul_right (a + b) (show 2 ≤ a by omega)
      omega
    calc
      (b + 1) ^ a + a + (b + 1) ≤ a * b ^ a + a * (a + b) := by omega
      _ = a * (b ^ a + a + b) := by ring
      _ < a * a ^ b := Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by omega)
      _ = a ^ (b + 1) := by rw [pow_succ, mul_comm]

private theorem gap_for_two {b : ℕ} (hb : 6 ≤ b) :
    b ^ 2 + 2 + b < 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
    have hlin : 3 * b ≤ b ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right b (show 3 ≤ b by omega)
    have hsquare : (b+1)^2 ≤ 2*b^2 := by nlinarith only [hlin, hb]
    calc
      (b + 1) ^ 2 + 2 + (b + 1) ≤ 2 * (b ^ 2 + 2 + b) := by omega
      _ < 2 * 2 ^ b := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 2 ^ (b + 1) := by rw [pow_succ, mul_comm]

theorem OMA.solution : type_of% @OMA.S_mse_3290080.main := by
  intro a b ha hb hab
  constructor
  · intro h
    by_cases ha1 : a = 1
    · subst a
      simp at h
      omega
    by_cases hb1 : b = 1
    · subst b
      simp at h
      omega
    by_cases ha2 : a = 2
    · subst a
      have hb3 : 3 ≤ b := by omega
      by_cases hb5 : b ≤ 5
      · interval_cases b <;> norm_num at *
      · have hgap := gap_for_two (show 6 ≤ b by omega)
        omega
    by_cases hb2 : b = 2
    · subst b
      have ha3 : 3 ≤ a := by omega
      by_cases ha5 : a ≤ 5
      · interval_cases a <;> norm_num at h
      · have hgap := gap_for_two (show 6 ≤ a by omega)
        omega
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have hgap := gap_for_three_or_more (show 3 ≤ a by omega) hlt
      omega
    · have hgap := gap_for_three_or_more (show 3 ≤ b by omega) hgt
      omega
  · rintro ⟨rfl, rfl⟩
    decide
