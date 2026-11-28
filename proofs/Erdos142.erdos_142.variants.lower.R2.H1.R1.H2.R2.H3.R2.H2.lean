import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

-- Scratch proof for Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H2
-- Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e))

namespace ScratchStretchedExpSummable

open Filter Real

theorem stretched_exp_summable :
    ∀ C c e : ℝ, 0 < C → 0 < c → 0 < e →
      Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e)) := by
  intro C c e hC hc he
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hconst : 0 < c * (Real.log 4) ^ e := mul_pos hc (Real.rpow_pos_of_pos hlog4 e)
  have hlim : Tendsto (fun j : ℕ => (2 : ℝ) * Real.log (j : ℝ) / ((j : ℝ) ^ e)) atTop (nhds 0) := by
    have h1 := (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    simpa [mul_div_assoc] using h1.const_mul (2 : ℝ)
  have hp : Summable (fun j : ℕ => C * ((j : ℝ) ^ (2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).mul_left C
  refine Summable.of_norm_bounded_eventually_nat hp ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlim.eventually (gt_mem_nhds hconst)] with j hj hlt
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hje : (0 : ℝ) < (j : ℝ) ^ e := Real.rpow_pos_of_pos hjpos e
  rw [Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hdiv : 2 * Real.log (j : ℝ) < c * (Real.log 4) ^ e * (j : ℝ) ^ e := by
    exact (div_lt_iff₀ hje).mp hlt
  have hmulpow : ((j : ℝ) * Real.log 4) ^ e = (j : ℝ) ^ e * (Real.log 4) ^ e :=
    Real.mul_rpow hjpos.le hlog4.le
  have hexp_le : -c * ((j : ℝ) * Real.log 4) ^ e ≤ -(2 * Real.log (j : ℝ)) := by
    rw [hmulpow]
    linarith
  calc Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e)
      ≤ Real.exp (-(2 * Real.log (j : ℝ))) := Real.exp_le_exp.mpr hexp_le
    _ = (Real.exp (2 * Real.log (j : ℝ)))⁻¹ := Real.exp_neg _
    _ = ((j : ℝ) ^ (2 : ℝ))⁻¹ := by
        congr 1
        rw [Real.rpow_def_of_pos hjpos, mul_comm]

end ScratchStretchedExpSummable

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := ScratchStretchedExpSummable.stretched_exp_summable
