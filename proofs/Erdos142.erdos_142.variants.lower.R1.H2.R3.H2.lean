import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R1.H2.R3.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R1.H2.R3
-- Shorter proof: exp(-c*y) = o(y^(-A/ε)) (isLittleO_exp_neg_mul_rpow_atTop) composed with y = (log N)^ε.
-- Credit: @Cryptokraken974

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H2 := by
  intro A C c ε _ hC hc hε
  have hl : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [((isLittleO_exp_neg_mul_rpow_atTop hc (-(A / ε))).comp_tendsto
    ((tendsto_rpow_atTop hε).comp hl)).def (inv_pos.2 hC), hl.eventually_gt_atTop 0] with N h hL
  simp only [Function.comp, norm_eq_abs, abs_exp, ← rpow_mul hL.le] at h
  rw [show ε * -(A / ε) = -A by field_simp, rpow_neg hL.le] at h
  simpa [hC.ne', abs_of_pos (rpow_pos_of_pos hL A)] using mul_le_mul_of_nonneg_left h hC.le
