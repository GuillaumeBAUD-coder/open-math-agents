import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2
-- Credit: @LAPRAI

open Real Filter

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e hC hc he
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hx : Tendsto (fun j : ℕ => ((j : ℝ) * Real.log 4) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop.atTop_mul_const hL)
  have h1 := ((tendsto_exp_mul_div_rpow_atTop (2 / e) c hc).comp hx).eventually_ge_atTop C
  have hG : Summable (fun j : ℕ => (((j : ℝ) * Real.log 4) ^ 2)⁻¹) := by
    simp_rw [mul_pow, mul_inv]
    exact (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  refine Summable.of_norm_bounded_eventually_nat hG ?_
  filter_upwards [h1, eventually_gt_atTop 0] with j hj hj0
  simp only [Function.comp] at hj
  have hjpos : (0 : ℝ) < j * Real.log 4 := mul_pos (by exact_mod_cast hj0) hL
  have hpow : (((j : ℝ) * Real.log 4) ^ e) ^ (2 / e) = ((j : ℝ) * Real.log 4) ^ 2 := by
    rw [← Real.rpow_mul hjpos.le, show e * (2 / e) = (2 : ℝ) by field_simp, Real.rpow_two]
  rw [hpow] at hj
  have hq : 0 < ((j : ℝ) * Real.log 4) ^ 2 := by positivity
  rw [le_div_iff₀ hq] at hj
  have hE : 0 < Real.exp (c * ((j : ℝ) * Real.log 4) ^ e) := Real.exp_pos _
  rw [Real.norm_of_nonneg (by positivity), neg_mul, Real.exp_neg, ← div_eq_mul_inv,
    div_le_iff₀ hE, inv_mul_eq_div, le_div_iff₀ hq]
  exact hj

