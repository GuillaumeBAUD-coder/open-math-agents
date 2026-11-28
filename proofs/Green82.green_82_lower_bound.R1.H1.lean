import OMAReductions.R_Green82_green_82_lower_bound_R1

-- Step Green82.green_82_lower_bound.R1.H1: hypothesis H1 of reduction Green82.green_82_lower_bound.R1
-- Credit: @luciusacarr
-- Take o n = (log M + |log c|) / M with M = log (log (log n)); then
-- (log log n) ^ (1 - o n) = log log n / (M * exp |log c|) ≤ c * log log n / M.

open Filter Real Asymptotics
open scoped Topology

theorem OMA.solution : OMA.R_Green82_green_82_lower_bound_R1.H1 := by
  intro c hc
  have ha : 0 ≤ |Real.log c| := abs_nonneg _
  have hT2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hT : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hT2
  refine ⟨fun n => (Real.log (Real.log (Real.log (Real.log (n : ℝ)))) + |Real.log c|) /
      Real.log (Real.log (Real.log (n : ℝ))), ?_, ?_⟩
  · have hf : Tendsto (fun x : ℝ => (Real.log x + |Real.log c|) / x) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h2 : Tendsto (fun x : ℝ => |Real.log c| / x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h3 := h1.add h2
      rw [add_zero] at h3
      refine h3.congr' ?_
      filter_upwards with x
      rw [add_div]
    rw [Asymptotics.isLittleO_one_iff]
    exact hf.comp hT
  · filter_upwards [hT.eventually_ge_atTop 1, hT2.eventually_gt_atTop 0] with n hn hL0
    generalize hL : Real.log (Real.log (n : ℝ)) = L at hn hL0 ⊢
    generalize hM : Real.log L = M at hn ⊢
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hn
    have hM0 : 0 < M := by linarith
    rw [abs_of_nonneg (div_nonneg (by linarith) hM0.le)]
    rw [Real.rpow_sub hL0, Real.rpow_one, Real.rpow_def_of_pos hL0, hM]
    have hmul : M * ((Real.log M + |Real.log c|) / M) = Real.log M + |Real.log c| := by
      field_simp
    rw [hmul, Real.exp_add, Real.exp_log hM0]
    have hca : 1 ≤ c * Real.exp |Real.log c| := by
      have h1 : Real.exp (-|Real.log c|) ≤ c := by
        calc Real.exp (-|Real.log c|) ≤ Real.exp (Real.log c) :=
              Real.exp_le_exp.mpr (by have := neg_abs_le (Real.log c); linarith)
          _ = c := Real.exp_log hc
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos |Real.log c|).le
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
    rw [div_le_div_iff₀ (by positivity) hM0]
    calc L * M = L * M * 1 := by ring
      _ ≤ L * M * (c * Real.exp |Real.log c|) :=
          mul_le_mul_of_nonneg_left hca (by positivity)
      _ = c * L * (M * Real.exp |Real.log c|) := by ring
