import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

/-! Compare the exponential against powers using the Mathlib growth limit.
Builds on Raimo33’s proof in PR 18783 and weizj99’s revision in PR 32292. -/
open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ _ hc hε
  have l := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [((tendsto_exp_mul_div_rpow_atTop (A / ε) c hc).comp
    ((tendsto_rpow_atTop hε).comp l)).eventually_ge_atTop C, l.eventually_gt_atTop 0] with N hN hL
  change 0 < log (N : ℝ) at hL
  have hpow := rpow_pos_of_pos hL A
  simp only [Function.comp_apply] at hN
  rw [← rpow_mul hL.le, show ε * (A / ε) = A by field_simp] at hN
  rw [neg_mul, exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) hpow, one_mul]
  exact (le_div_iff₀ hpow).mp hN
