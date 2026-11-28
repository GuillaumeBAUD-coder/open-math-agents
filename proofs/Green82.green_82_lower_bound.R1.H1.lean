import OMAReductions.R_Green82_green_82_lower_bound_R1
import Mathlib

-- Credit: @LordMike

open Filter Topology Asymptotics

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H1 := by
  unfold OMA.R_Green82_green_82_lower_bound_R1.H1
  intro c hc
  have hL : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hM : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hdiv : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (Real.log (n : ℝ)))) /
      Real.log (Real.log (Real.log (n : ℝ)))) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hM
  refine ⟨fun n : ℕ => (Real.log (Real.log (Real.log (Real.log (n : ℝ)))) + |Real.log c| + 1) /
    Real.log (Real.log (Real.log (n : ℝ))), ?_, ?_⟩
  · refine (Asymptotics.isLittleO_one_iff _).2 ?_
    have h2 : Tendsto (fun n : ℕ => (|Real.log c| + 1) / Real.log (Real.log (Real.log (n : ℝ))))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hM
    have h3 := hdiv.add h2
    rw [add_zero] at h3
    refine Tendsto.congr (fun n => ?_) h3
    try dsimp only
    ring
  · filter_upwards [hL.eventually_gt_atTop 0, hM.eventually_ge_atTop 1] with n hLn hM1
    try dsimp only
    set L := Real.log (Real.log (n : ℝ)) with hLdef
    set M := Real.log L with hMdef
    have hM0 : 0 < M := by linarith
    have hMne : M ≠ 0 := hM0.ne'
    have hcne : c ≠ 0 := hc.ne'
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hnum : 0 ≤ Real.log M + |Real.log c| + 1 := by
      linarith [abs_nonneg (Real.log c)]
    rw [abs_of_nonneg (div_nonneg hnum hM0.le)]
    rw [Real.rpow_sub hLn, Real.rpow_one, Real.rpow_def_of_pos hLn, ← hMdef]
    have hprod : M * ((Real.log M + |Real.log c| + 1) / M) = Real.log M + |Real.log c| + 1 := by
      field_simp
    have hkey : M / c ≤ Real.exp (M * ((Real.log M + |Real.log c| + 1) / M)) := by
      rw [hprod]
      have h2 : M / c = Real.exp (Real.log M - Real.log c) := by
        rw [Real.exp_sub, Real.exp_log hM0, Real.exp_log hc]
      rw [h2]
      apply Real.exp_le_exp.mpr
      linarith [neg_le_abs (Real.log c), abs_nonneg (Real.log c)]
    calc L / Real.exp (M * ((Real.log M + |Real.log c| + 1) / M))
        ≤ L / (M / c) := div_le_div_of_nonneg_left hLn.le (div_pos hM0 hc) hkey
      _ = c * L / M := by rw [div_div_eq_mul_div]; ring
