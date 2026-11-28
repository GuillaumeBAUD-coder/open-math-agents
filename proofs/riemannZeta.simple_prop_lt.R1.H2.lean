import OMAReductions.R_riemannZeta_simple_prop_lt_R1

open ZetaZeros

theorem OMA.solution : OMA.R_riemannZeta_simple_prop_lt_R1.H2 := by
  show (let H : ℝ :=
    3 / 2 - (Real.sqrt 2)⁻¹ *
      (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)
    H = 2 - montgomeryTaylorConst⁻¹ ∧ (1 / 2 : ℝ) < H)
  intro H
  have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx0 : (0:ℝ) < (Real.sqrt 2)⁻¹ := inv_pos.mpr hs2
  have hx1 : (Real.sqrt 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num))
  have hxpi : (Real.sqrt 2)⁻¹ < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsin : 0 < Real.sin (Real.sqrt 2)⁻¹ := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hcos : 0 < Real.cos (Real.sqrt 2)⁻¹ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩
  have htan : (Real.sqrt 2)⁻¹ < Real.tan (Real.sqrt 2)⁻¹ := Real.lt_tan hx0 hxpi
  rw [Real.tan_eq_sin_div_cos] at htan
  constructor
  · simp only [H, montgomeryTaylorConst, one_div, Real.tan_eq_sin_div_cos]
    generalize Real.sin (Real.sqrt 2)⁻¹ = s at *
    generalize Real.cos (Real.sqrt 2)⁻¹ = c at *
    generalize Real.sqrt 2 = r at *
    field_simp
    linear_combination (-s) * hsq
  · simp only [H]
    rw [lt_div_iff₀ hcos] at htan
    have : (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) < 1 := by
      rw [← mul_div_assoc, div_lt_one hsin]; linarith
    linarith
