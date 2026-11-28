import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R2.H3.R2.H2
-- Credit: @jktcv2kz4f-cyber

open Filter Real

namespace OMA.Helpers

lemma one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have h : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log 4 := (Real.log_lt_log (Real.exp_pos 1) h).le

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 := by
  intro C c e hC hc he
  apply Summable.mul_left C
  have hp : Summable (fun j : ℕ ↦ ((j : ℝ) ^ 2)⁻¹) := by
    simpa only [Real.rpow_two] using
      (Real.summable_nat_rpow_inv (p := (2 : ℝ))).mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hp ?_
  have hlo : (fun x : ℝ ↦ Real.log x) =o[atTop] (fun x : ℝ ↦ x ^ e) :=
    isLittleO_log_rpow_atTop he
  have hev : ∀ᶠ j : ℕ in atTop, ‖Real.log (j : ℝ)‖ ≤ (c / 2) * ‖(j : ℝ) ^ e‖ :=
    tendsto_natCast_atTop_atTop.eventually (hlo.bound (by positivity : 0 < c / 2))
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with j hj hj1
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1r : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hlog_nonneg : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hj1r
  have hpow_nonneg : 0 ≤ (j : ℝ) ^ e := Real.rpow_nonneg hjpos.le e
  rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hpow_nonneg] at hj
  have h4 : (j : ℝ) ≤ (j : ℝ) * Real.log 4 := by
    nlinarith [OMA.Helpers.one_le_log_four, hjpos]
  have hpow_le : (j : ℝ) ^ e ≤ ((j : ℝ) * Real.log 4) ^ e :=
    Real.rpow_le_rpow hjpos.le h4 he.le
  have hexp_le : 2 * Real.log (j : ℝ) ≤ c * ((j : ℝ) * Real.log 4) ^ e := by
    nlinarith [mul_le_mul_of_nonneg_left hpow_le hc.le]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hinv : ((j : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log (j : ℝ))) := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log (j : ℝ) = ((2 : ℕ) : ℝ) * Real.log (j : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hjpos]
  rw [hinv]
  apply Real.exp_le_exp.mpr
  linarith
