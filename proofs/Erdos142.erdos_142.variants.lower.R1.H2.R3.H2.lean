import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3
-- Shorter proof: exp (c y) / y ^ (A / ε) → ∞ along y = (log N) ^ ε.
-- Credit: @Sebastian-J-U

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have h : Tendsto (fun N : ℕ => log N) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp ((tendsto_rpow_atTop hε).comp h)).eventually_ge_atTop C, h.eventually_gt_atTop 0] with N hN hL
  simp only [Function.comp, ← rpow_mul hL.le, mul_div_cancel₀ _ hε.ne'] at hN
  rwa [neg_mul, exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), one_div_mul_eq_div]
