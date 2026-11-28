import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

namespace OMA.Helpers

open Filter Asymptotics

theorem e142_stretchedExp_log4_summable (C c e : ℝ) (hC : 0 < C) (hc : 0 < c) (he : 0 < e) :
    Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e)) := by
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ha : 0 < c * Real.log 4 ^ e := mul_pos hc (Real.rpow_pos_of_pos hl4 e)
  have hg : Summable (fun j : ℕ ↦ C * (j : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hlog := (isLittleO_log_rpow_atTop he).bound (half_pos ha)
  have hN := tendsto_natCast_atTop_atTop.eventually hlog
  filter_upwards [hN, eventually_ge_atTop 1] with j hj hj1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  refine (Real.norm_of_nonneg (by positivity)).le.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  rw [Real.mul_rpow hjpos.le hl4.le, Real.rpow_def_of_pos hjpos (-2)]
  apply Real.exp_le_exp.mpr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hjpos e)] at hj
  have h1 := le_abs_self (Real.log j)
  have h2 : -c * ((j : ℝ) ^ e * Real.log 4 ^ e) = -((c * Real.log 4 ^ e) * (j : ℝ) ^ e) := by ring
  rw [h2]
  linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 :=
  fun C c e hC hc he => OMA.Helpers.e142_stretchedExp_log4_summable C c e hC hc he
