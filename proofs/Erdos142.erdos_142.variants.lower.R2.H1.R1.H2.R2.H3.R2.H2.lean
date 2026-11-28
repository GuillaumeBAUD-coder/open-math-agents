import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

-- Credit: @midnitefox. Applies the Mathlib little-o estimate directly on the scaled power.
open Filter Real in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e _ hc he
  have h : 0 < log 4 := by positivity
  refine (summable_of_isBigO_nat ?_ ((isLittleO_exp_neg_mul_rpow_atTop hc (-2/e)).isBigO.comp_tendsto
    ((tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop.atTop_mul_const h)))).mul_left C
  refine ((summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)).mul_right
    (log 4 ^ (-2 : ℝ))).congr fun j ↦ ?_
  dsimp
  rw [← rpow_mul (by positivity), show e * (-2/e) = -2 by field_simp,
    mul_rpow (Nat.cast_nonneg _) h.le]
