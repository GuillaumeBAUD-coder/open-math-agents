import OMAReductions.R_Mills_lower_bound_of_RH_R1

/-! Use the Costa–Pereira inequality for the three roots and the elementary
bound ψ(y) ≤ 2.9 y. At x ≥ 599 the cubic and fifth roots together cost
at most 0.65 times the square root. -/

open Real Chebyshev

private lemma psi_linear {y : ℝ} (hy : 1 ≤ y) : psi y ≤ 2.9 * y := by
  have ypos : 0 < y := by linarith
  have s := sqrt_pos.mpr ypos
  have e := exp_pos 1
  have ht := log_le_sub_one_of_pos (div_pos s e)
  rw [log_div s.ne' e.ne', log_exp, log_sqrt ypos.le] at ht
  have hlog : log y ≤ (2 / exp 1) * sqrt y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ e]
    have ht' : log y / 2 ≤ sqrt y / exp 1 := by linarith
    have := (le_div_iff₀ e).mp ht'
    linarith
  have h4 : log 4 ≤ 1.4 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, log_pow]
    linarith [log_two_lt_d9]
  have ce : 4 / exp 1 ≤ 1.5 := (div_le_iff₀ e).mpr (by linarith [exp_one_gt_d9])
  calc
    _ ≤ log 4 * y + 2 * sqrt y * log y := psi_le hy
    _ ≤ 1.4 * y + 2 * sqrt y * ((2/exp 1) * sqrt y) := by gcongr
    _ = 1.4 * y + (4/exp 1) * y := by rw [← Real.sq_sqrt ypos.le]; ring_nf; simp [Real.sq_sqrt ypos.le]
    _ ≤ 2.9 * y := by nlinarith [mul_le_mul_of_nonneg_right ce ypos.le]

theorem OMA.solution : OMA.R_Mills_lower_bound_of_RH_R1.H2 := by
  intro x hx
  have xpos : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have hlog : 6.2 ≤ log x := by
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^9) (by linarith : (2 : ℝ)^9 ≤ x)
    rw [log_pow] at h
    norm_num at h
    linarith [log_two_gt_d9]
  have rootBound (n : ℕ) (c : ℝ) (hn : n ≠ 0) (hc : 0 < c) (hpow : c^n ≤ x) :
      c ≤ x ^ (1 / (n : ℝ)) := by
    calc
      c = (c^(n : ℝ))^(1/(n : ℝ)) := by
        rw [← rpow_mul hc.le]
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp
        simp
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow) (by positivity)
  have h6 := rootBound 6 2.5 (by decide) (by norm_num) (by linarith)
  have h4 := rootBound 4 4 (by decide) (by norm_num) (by linarith)
  have c3 : x ^ (3 : ℝ)⁻¹ ≤ 0.4 * sqrt x := by
    have h := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg xpos.le (3 : ℝ)⁻¹)
    rw [← rpow_add xpos] at h
    norm_num at h
    rw [Real.sqrt_eq_rpow]
    linarith
  have c5 : x ^ (5 : ℝ)⁻¹ ≤ 0.25 * sqrt x := by
    have h := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg xpos.le (1/4 : ℝ))
    rw [← rpow_add xpos] at h
    norm_num at h
    have hc := Real.rpow_le_rpow_of_exponent_le x1 (by norm_num : (5 : ℝ)⁻¹ ≤ 1/4)
    rw [Real.sqrt_eq_rpow]
    linarith
  have bound (n : ℝ) (hn : 0 < n) := psi_linear (Real.one_le_rpow x1 (inv_nonneg.mpr hn.le))
  have a := bound 2 (by norm_num)
  have b := bound 3 (by norm_num)
  have c := bound 5 (by norm_num)
  have h := psi_sub_theta_le_psi_add_psi_add_psi x
  rw [← one_div, ← sqrt_eq_rpow] at a h
  have hlog2 : 6.2^2 ≤ (log x)^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 6.2) hlog]
  have hs := sqrt_nonneg x
  nlinarith [mul_le_mul_of_nonneg_right hlog2 hs]
