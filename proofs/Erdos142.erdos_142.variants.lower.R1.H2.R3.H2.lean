import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3
-- Credit: @Raimo33

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε hA hC hc hε
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := ((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp hlog)).eventually_ge_atTop C
  filter_upwards [h1, hlog.eventually_gt_atTop 0] with N hN hL
  simp only [Function.comp] at hN
  set L := log (N : ℝ)
  have hLA := rpow_pos_of_pos hL A
  rw [← rpow_mul hL.le, show ε * (A / ε) = A by field_simp, le_div_iff₀ hLA] at hN
  rw [le_div_iff₀ hLA, neg_mul, exp_neg]
  calc _ = (C * L ^ A) / exp (c * L ^ ε) := by rw [div_eq_mul_inv]; ring
       _ ≤ 1 := (div_le_one (exp_pos _)).2 hN
