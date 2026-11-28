import OMAReductions.R_Erdos1081_erdos_1081_R1

-- Credit: @LordMike

open Filter in
theorem OMA.solution : OMA.R_Erdos1081_erdos_1081_R1.H2 := by
  intro a C ha
  have hf : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hw : Tendsto (fun x : ℝ => a * Real.log (Real.log x)) atTop atTop :=
    hf.const_mul_atTop ha
  have h1 := ((tendsto_exp_div_rpow_atTop C).comp hw).const_mul_atTop
    (Real.rpow_pos_of_pos ha C)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
  have h1x : 1 < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hL : 0 < Real.log x := by linarith
  have hv : 0 < Real.log (Real.log x) := Real.log_pos h1x
  have key : Real.log x ^ a = Real.exp (a * Real.log (Real.log x)) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hL]
  have hac : 0 < a ^ C := Real.rpow_pos_of_pos ha C
  have hvc : 0 < Real.log (Real.log x) ^ C := Real.rpow_pos_of_pos hv C
  simp only [Function.comp_apply]
  rw [key, Real.mul_rpow ha.le hv.le]
  field_simp
