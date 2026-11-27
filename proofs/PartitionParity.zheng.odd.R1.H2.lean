import OMAReductions.R_PartitionParity_zheng_odd_R1

open Filter Asymptotics

theorem OMA.solution : OMA.R_PartitionParity_zheng_odd_R1.H2 := by
  intro f c hc hlim
  have hc2 : (0 : ℝ) < c / 2 := by positivity
  have hclt : ((c / 2 : ℝ) : EReal) < ((c : ℝ) : EReal) := by
    rw [EReal.coe_lt_coe_iff]
    linarith
  have hlt : ((c / 2 : ℝ) : EReal) <
      liminf (fun X : ℝ ↦ ((f X / Real.sqrt X : ℝ) : EReal)) atTop :=
    lt_of_lt_of_le hclt hlim
  have hev : ∀ᶠ X : ℝ in atTop,
      ((c / 2 : ℝ) : EReal) < ((f X / Real.sqrt X : ℝ) : EReal) :=
    eventually_lt_of_lt_liminf hlt
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / c, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with X hX hXpos
  have hratio : c / 2 < f X / Real.sqrt X := EReal.coe_lt_coe_iff.mp hX
  have hsqrt : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos_of_pos hXpos
  have h1 : (c / 2) * Real.sqrt X < f X := by
    have h := (lt_div_iff₀ hsqrt).mp hratio
    exact h
  have hfpos : (0 : ℝ) < f X := by
    have hpos : (0 : ℝ) < (c / 2) * Real.sqrt X := by positivity
    linarith
  have h2 : Real.sqrt X < (2 / c) * f X := by
    have h3 := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < 2 / c)
    have hrw : (2 / c) * ((c / 2) * Real.sqrt X) = Real.sqrt X := by
      field_simp
    rw [hrw] at h3
    exact h3
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg X), Real.norm_of_nonneg hfpos.le]
  exact h2.le
