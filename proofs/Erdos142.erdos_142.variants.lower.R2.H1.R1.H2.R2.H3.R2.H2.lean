import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H2
-- Credit: @mijuny

open Real Filter

namespace Pre36621

theorem prove_H2 :
    OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e hC hc he
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlin : Tendsto (fun j : ℕ => (j : ℝ) * Real.log 4) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlog4
  have ht : Tendsto (fun j : ℕ => ((j : ℝ) * Real.log 4) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp hlin
  let B : ℝ := C / (Real.log 4) ^ (2 : ℝ)
  have h1 := ((tendsto_exp_mul_div_rpow_atTop (2 / e) c hc).comp ht).eventually_ge_atTop B
  have hp : Summable (fun j : ℕ => ((j : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hp ?_
  filter_upwards [h1, eventually_gt_atTop 0] with j hj hj0
  simp only [Function.comp] at hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
  have hprod : 0 < (j : ℝ) * Real.log 4 := mul_pos hjpos hlog4
  have hpow : (((j : ℝ) * Real.log 4) ^ e) ^ (2 / e) = ((j : ℝ) * Real.log 4) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hprod.le]
    congr 1
    field_simp [he.ne']
  rw [hpow] at hj
  have hden : 0 < ((j : ℝ) * Real.log 4) ^ (2 : ℝ) := Real.rpow_pos_of_pos hprod 2
  have hle1 : B * ((j : ℝ) * Real.log 4) ^ (2 : ℝ) ≤ Real.exp (c * ((j : ℝ) * Real.log 4) ^ e) :=
    (le_div_iff₀ hden).mp hj
  have hmul_rpow : ((j : ℝ) * Real.log 4) ^ (2 : ℝ) = (j : ℝ) ^ (2 : ℝ) * (Real.log 4) ^ (2 : ℝ) :=
    Real.mul_rpow hjpos.le hlog4.le
  have hlhs : B * ((j : ℝ) * Real.log 4) ^ (2 : ℝ) = C * (j : ℝ) ^ (2 : ℝ) := by
    dsimp [B]
    rw [hmul_rpow]
    field_simp [(Real.rpow_pos_of_pos hlog4 2).ne']
  rw [hlhs] at hle1
  rw [Real.norm_of_nonneg (by positivity), neg_mul, Real.exp_neg]
  have hj2_pos : 0 < (j : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hjpos 2
  calc C * (Real.exp (c * ((j : ℝ) * Real.log 4) ^ e))⁻¹
      = C / Real.exp (c * ((j : ℝ) * Real.log 4) ^ e) := by ring
    _ ≤ C / (C * (j : ℝ) ^ (2 : ℝ)) :=
        div_le_div_of_nonneg_left hC.le (mul_pos hC hj2_pos) hle1
    _ = ((j : ℝ) ^ (2 : ℝ))⁻¹ := by field_simp [hC.ne']

end Pre36621

theorem OMA.solution :
    OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 :=
  Pre36621.prove_H2
