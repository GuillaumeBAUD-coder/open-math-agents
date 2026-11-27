import OMAReductions.R_PartitionParity_zheng_odd_R1

-- Step PartitionParity.zheng.odd.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

theorem OMA.solution : OMA.R_PartitionParity_zheng_odd_R1.H2 := by
  intro f c hc hlim
  have hlt : (((c / 2 : ℝ) : EReal)) < liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) atTop := by
    refine lt_of_lt_of_le ?_ hlim
    exact_mod_cast (by linarith : c / 2 < c)
  have hev : ∀ᶠ X : ℝ in atTop, ((c / 2 : ℝ) : EReal) < ((f X / Real.sqrt X : ℝ) : EReal) :=
    Filter.eventually_lt_of_lt_liminf hlt
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / c, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hX' : c / 2 < f X / Real.sqrt X := by exact_mod_cast hX
  have hsqrt_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have hf_pos : 0 < f X := by
    have : (c / 2) * Real.sqrt X < f X := (lt_div_iff₀ hsqrt_pos).mp hX'
    nlinarith
  rw [Real.norm_of_nonneg (le_of_lt hsqrt_pos), Real.norm_of_nonneg (le_of_lt hf_pos)]
  have hmul : (c / 2) * Real.sqrt X < f X := (lt_div_iff₀ hsqrt_pos).mp hX'
  have h2c : (2 / c) * ((c / 2) * Real.sqrt X) = Real.sqrt X := by
    field_simp [hc.ne']
  have hle : (2 / c) * ((c / 2) * Real.sqrt X) ≤ (2 / c) * f X :=
    mul_le_mul_of_nonneg_left (le_of_lt hmul) (by positivity)
  linarith
