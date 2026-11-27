import OMAReductions.R_Erdos830_erdos_830_variants_pomerance_R1

-- Step Erdos830.erdos_830.variants.pomerance.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_pomerance_R1.H2 := by
  intro o ho
  have ho_small : ∀ᶠ x : ℝ in atTop, ‖o x‖ ≤ (1 / 4 : ℝ) * ‖(1 : ℝ)‖ :=
    ho.bound (by norm_num)
  have hlog1 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hlog3 : ∀ᶠ x : ℝ in atTop, (16 : ℝ) ≤ Real.log (Real.log (Real.log x)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).eventually_ge_atTop 16
  filter_upwards [ho_small, eventually_ge_atTop (0 : ℝ), hlog1, hlog3] with x hox hx0 hlx hl3
  rw [Real.norm_eq_abs, norm_one, mul_one] at hox
  have hcoeff : (1 / 4 : ℝ) ≤ 1 / 2 + o x := by linarith [(abs_le.mp hox).1]
  have hsqrt : 4 * Real.sqrt (Real.log x) ≤
      Real.sqrt (Real.log x * Real.log (Real.log (Real.log x))) := by
    have hmul : Real.log x * 16 ≤ Real.log x * Real.log (Real.log (Real.log x)) :=
      mul_le_mul_of_nonneg_left hl3 (by linarith)
    calc 4 * Real.sqrt (Real.log x)
        = Real.sqrt (Real.log x * 16) := by
          rw [Real.sqrt_mul (by linarith), show Real.sqrt 16 = 4 by norm_num]
          ring
      _ ≤ Real.sqrt (Real.log x * Real.log (Real.log (Real.log x))) := Real.sqrt_le_sqrt hmul
  have hroot : Real.nthRoot 3 (Real.log x) ≤ Real.sqrt (Real.log x) := by
    rw [Real.nthRoot_of_nonneg (by linarith), Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlx (by norm_num)
  have hexp_le : Real.nthRoot 3 (Real.log x) ≤
      (1 / 2 + o x) * Real.sqrt (Real.log x * Real.log (Real.log (Real.log x))) := by
    nlinarith [Real.sqrt_nonneg (Real.log x)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx0
